package main

import (
	"bufio"
	"bytes"
	"crypto/rand"
	"crypto/sha3"
	"crypto/tls"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"net"
	"net/textproto"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	"golang.org/x/crypto/argon2"
	"golang.org/x/crypto/chacha20"
	"golang.org/x/net/proxy"
)

// Config holds all command line configuration
type Config struct {
	Key        string // esub encryption key
	To         string // Recipient for email mode
	FromHeader string // Custom From: header (empty for default)
	Newsgroups string // Newsgroups to post to or read from
	BlockSize  int    // Block size in KB for splitting files
	Send       bool   // Send mode flag
	Receive    bool   // Receive mode flag
	NNTP       string // NNTP server address
	ProxyPort  int    // SOCKS5 proxy port (default 9050 for Tor)
	EmailMode  bool   // Email mode (no From: header)
	Username   string // NNTP username for authentication
	Password   string // NNTP password for authentication
	UseTLS     bool   // Use TLS for NNTP connection
	Days       int    // Download articles from last N days
	Latest     bool   // Only fetch articles newer than last run
	MaxBatch   int    // Maximum batch size for XOVER command
	Timeout    int    // Read timeout in seconds
}

// Esub handles esub generation and validation
type Esub struct {
	key string // Encryption key for esub
}

// Article represents a single Usenet article
type Article struct {
	Header   textproto.MIMEHeader // Article headers
	Body     []byte               // Article body (binary data)
	Part     int                  // Part number (e.g., 1/10)
	Total    int                  // Total parts
	Filename string               // Original filename
	Number   string               // Article number from server
	Date     time.Time            // Article date
	Esub     string               // esub value
	Hash     string               // Content hash for deduplication
}

// GroupState tracks the state of each newsgroup for resuming downloads
type GroupState struct {
	LastArticle int       `json:"last_article"`
	LastFetch   time.Time `json:"last_fetch"`
}

// CacheEntry represents an entry in the replay cache
type CacheEntry struct {
	Esub      string    `json:"esub"`
	Timestamp time.Time `json:"timestamp"`
}

// FileCacheEntry represents a cached file part
type FileCacheEntry struct {
	Filename    string    `json:"filename"`
	TotalParts  int       `json:"total_parts"`
	PartNumber  int       `json:"part_number"`
	Esub        string    `json:"esub"`
	ContentHash string    `json:"content_hash"`
	FirstSeen   time.Time `json:"first_seen"`
	LastSeen    time.Time `json:"last_seen"`
}

// ManifestEntry represents an entry in the manifest file for reconstruction
type ManifestEntry struct {
	ArticleFile  string `json:"article_file"`  // e.g., "0001.txt"
	OriginalFile string `json:"original_file"` // e.g., "archive.zip"
	PartNumber   int    `json:"part_number"`   // e.g., 1
	TotalParts   int    `json:"total_parts"`   // e.g., 10
	Esub         string `json:"esub"`          // esub value for this article
	BlockSizeKB  int    `json:"block_size_kb"` // Block size used
}

// Global variables
var (
	rcFlag    = flag.Bool("rc", false, "enable replay cache")
	dbPath    = flag.String("dbpath", "", "custom path for replay cache database")
	cache     *Cache
	state     = make(map[string]GroupState) // Newsgroup state
	stateMutex sync.RWMutex                 // Mutex for state
)

// Cache implements a file-based cache without SQLite
type Cache struct {
	ReplayCache map[string]CacheEntry    `json:"replay_cache"`
	FileCache   map[string]FileCacheEntry `json:"file_cache"`
	mu          sync.RWMutex
	filePath    string
}

// NewCache creates a new file-based cache
func NewCache(filePath string) (*Cache, error) {
	c := &Cache{
		ReplayCache: make(map[string]CacheEntry),
		FileCache:   make(map[string]FileCacheEntry),
		filePath:    filePath,
	}
	
	if err := c.Load(); err != nil && !os.IsNotExist(err) {
		return nil, err
	}
	
	return c, nil
}

// Load loads cache from disk
func (c *Cache) Load() error {
	c.mu.Lock()
	defer c.mu.Unlock()
	
	data, err := os.ReadFile(c.filePath)
	if err != nil {
		return err
	}
	
	return json.Unmarshal(data, c)
}

// Save saves cache to disk
func (c *Cache) Save() error {
	c.mu.Lock()
	defer c.mu.Unlock()
	
	// Create directory if it doesn't exist
	if dir := filepath.Dir(c.filePath); dir != "" {
		if err := os.MkdirAll(dir, 0755); err != nil {
			return err
		}
	}
	
	data, err := json.MarshalIndent(c, "", "  ")
	if err != nil {
		return err
	}
	
	// Write atomically
	tempFile := c.filePath + ".tmp"
	if err := os.WriteFile(tempFile, data, 0644); err != nil {
		return err
	}
	
	return os.Rename(tempFile, c.filePath)
}

// AddReplay adds an esub to replay cache
func (c *Cache) AddReplay(esub string) {
	if !*rcFlag {
		return
	}
	
	c.mu.Lock()
	c.ReplayCache[esub] = CacheEntry{
		Esub:      esub,
		Timestamp: time.Now(),
	}
	c.mu.Unlock()
}

// HasReplay checks if esub is in replay cache
func (c *Cache) HasReplay(esub string) bool {
	if !*rcFlag {
		return false
	}
	
	c.mu.RLock()
	_, exists := c.ReplayCache[esub]
	c.mu.RUnlock()
	
	return exists
}

// AddFile adds a file part to file cache with improved key
func (c *Cache) AddFile(filename string, partNumber, totalParts int, esub, contentHash string) {
	if !*rcFlag {
		return
	}
	
	// Create a more specific key: filename + part + hash prefix
	key := fmt.Sprintf("%s:%d:%s", filename, partNumber, contentHash[:16])
	now := time.Now()
	
	c.mu.Lock()
	c.FileCache[key] = FileCacheEntry{
		Filename:    filename,
		TotalParts:  totalParts,
		PartNumber:  partNumber,
		Esub:        esub,
		ContentHash: contentHash,
		FirstSeen:   now,
		LastSeen:    now,
	}
	c.mu.Unlock()
}

// HasFile checks if file part is in cache with matching hash
func (c *Cache) HasFile(filename string, partNumber int, contentHash string) bool {
	if !*rcFlag {
		return false
	}
	
	// Create a more specific key: filename + part + hash prefix
	key := fmt.Sprintf("%s:%d:%s", filename, partNumber, contentHash[:16])
	
	c.mu.RLock()
	_, exists := c.FileCache[key]
	c.mu.RUnlock()
	
	return exists
}

// Cleanup removes old cache entries (older than 30 days)
func (c *Cache) Cleanup() {
	if !*rcFlag {
		return
	}
	
	cutoff := time.Now().AddDate(0, 0, -30)
	
	c.mu.Lock()
	defer c.mu.Unlock()
	
	// Clean replay cache
	for esub, entry := range c.ReplayCache {
		if entry.Timestamp.Before(cutoff) {
			delete(c.ReplayCache, esub)
		}
	}
	
	// Clean file cache
	for key, entry := range c.FileCache {
		if entry.LastSeen.Before(cutoff) {
			delete(c.FileCache, key)
		}
	}
}

// deriveKey generates an encryption key from the password using Argon2
func (e *Esub) deriveKey() []byte {
	salt := []byte("fixed-salt-1234") // Fixed salt for consistency
	return argon2.IDKey(
		[]byte(e.key),
		salt,
		3,      // iterations
		64*1024, // 64MB memory
		4,      // threads
		32,     // output key length (32 bytes for ChaCha20)
	)
}

// Generate creates a new unique esub for an article
func (e *Esub) Generate() (string, error) {
	// Generate random nonce
	nonce := make([]byte, 12)
	if _, err := rand.Read(nonce); err != nil {
		return "", fmt.Errorf("failed to generate nonce: %v", err)
	}

	// Derive encryption key
	key := e.deriveKey()
	
	// Create ChaCha20 cipher
	cipher, err := chacha20.NewUnauthenticatedCipher(key, nonce)
	if err != nil {
		return "", fmt.Errorf("failed to create cipher: %v", err)
	}

	// Hash "text" string as authentication token
	textHash := sha3.Sum256([]byte("text"))
	
	// Encrypt first 12 bytes of hash
	ciphertext := make([]byte, 12)
	cipher.XORKeyStream(ciphertext, textHash[:12])

	// Combine nonce and ciphertext as hex string
	return hex.EncodeToString(append(nonce, ciphertext...)), nil
}

// Validate checks if an esub was created with the given key
func (e *Esub) Validate(subject string) bool {
	// esub must be 48 hex chars (24 bytes)
	if len(subject) != 48 {
		return false
	}

	// Check replay cache first
	if cache != nil && cache.HasReplay(subject) {
		return false
	}

	// Decode hex string
	esubBytes, err := hex.DecodeString(subject)
	if err != nil || len(esubBytes) != 24 {
		return false
	}

	// Split into nonce and ciphertext
	nonce := esubBytes[:12]
	receivedCiphertext := esubBytes[12:]

	// Derive key and create cipher
	key := e.deriveKey()
	cipher, err := chacha20.NewUnauthenticatedCipher(key, nonce)
	if err != nil {
		return false
	}

	// Compute expected ciphertext
	textHash := sha3.Sum256([]byte("text"))
	expectedCiphertext := make([]byte, 12)
	cipher.XORKeyStream(expectedCiphertext, textHash[:12])

	// Compare ciphertexts
	if hex.EncodeToString(expectedCiphertext) == hex.EncodeToString(receivedCiphertext) {
		// Valid esub - add to cache
		if cache != nil {
			cache.AddReplay(subject)
		}
		return true
	}
	return false
}

// initCache initializes the file-based cache
func initCache() error {
	if !*rcFlag {
		return nil
	}

	// Determine cache file path
	path := *dbPath
	if path == "" {
		homeDir, err := os.UserHomeDir()
		if err != nil {
			// Fallback to current directory
			path = "./usenet_cache.json"
		} else {
			path = filepath.Join(homeDir, ".usenet_cache.json")
		}
	}

	var err error
	cache, err = NewCache(path)
	if err != nil {
		return fmt.Errorf("failed to initialize cache: %v", err)
	}

	// Clean old entries on startup
	cache.Cleanup()
	
	return nil
}

// loadState loads the state for a newsgroup from disk
func loadState(group string) error {
	stateFileName := fmt.Sprintf("%s.json", group)
	path := filepath.Join(".", stateFileName)
	data, err := os.ReadFile(path)
	if err != nil {
		if os.IsNotExist(err) {
			return nil // No state file exists yet
		}
		return fmt.Errorf("failed to read state file: %v", err)
	}

	stateMutex.Lock()
	defer stateMutex.Unlock()
	return json.Unmarshal(data, &state)
}

// saveState saves the state for a newsgroup to disk
func saveState(group string) error {
	stateFileName := fmt.Sprintf("%s.json", group)
	path := filepath.Join(".", stateFileName)
	
	stateMutex.RLock()
	data, err := json.MarshalIndent(state, "", "  ")
	stateMutex.RUnlock()
	if err != nil {
		return fmt.Errorf("failed to serialize state: %v", err)
	}

	// Write atomically
	tempFile := path + ".tmp"
	if err := os.WriteFile(tempFile, data, 0600); err != nil {
		return fmt.Errorf("failed to write temp state file: %v", err)
	}
	
	return os.Rename(tempFile, path)
}

// dialNNTP establishes a connection to an NNTP server, optionally via proxy
func dialNNTP(server string, useTLS bool, proxyAddr string) (net.Conn, error) {
	// Determine port if not specified
	address := server
	if !strings.Contains(server, ":") {
		if useTLS {
			address = fmt.Sprintf("%s:563", server) // NNTPS default port
		} else {
			address = fmt.Sprintf("%s:119", server) // NNTP default port
		}
	}

	// Connect via proxy if specified
	if proxyAddr != "" {
		dialer, err := proxy.SOCKS5("tcp", proxyAddr, nil, proxy.Direct)
		if err != nil {
			return nil, fmt.Errorf("proxy connection failed: %v", err)
		}
		conn, err := dialer.Dial("tcp", address)
		if err != nil {
			return nil, fmt.Errorf("proxy dial failed: %v", err)
		}

		// Wrap with TLS if needed
		if useTLS {
			return tls.Client(conn, &tls.Config{
				InsecureSkipVerify: true, // Accept self-signed certificates
				ServerName:         strings.Split(server, ":")[0],
			}), nil
		}
		return conn, nil
	}

	// Direct connection
	if useTLS {
		return tls.Dial("tcp", address, &tls.Config{
			InsecureSkipVerify: true,
		})
	}
	return net.Dial("tcp", address)
}

// authenticateNNTP authenticates with the NNTP server
func authenticateNNTP(conn net.Conn, username, password string) error {
	// Send username
	fmt.Fprintf(conn, "AUTHINFO USER %s\r\n", username)
	response, err := bufio.NewReader(conn).ReadString('\n')
	if err != nil {
		return fmt.Errorf("auth user read failed: %v", err)
	}
	if !strings.HasPrefix(response, "381") {
		return fmt.Errorf("auth user failed: %s", strings.TrimSpace(response))
	}

	// Send password
	fmt.Fprintf(conn, "AUTHINFO PASS %s\r\n", password)
	response, err = bufio.NewReader(conn).ReadString('\n')
	if err != nil {
		return fmt.Errorf("auth pass read failed: %v", err)
	}
	if !strings.HasPrefix(response, "281") {
		return fmt.Errorf("auth pass failed: %s", strings.TrimSpace(response))
	}
	return nil
}

// parseDate parses an NNTP date string
func parseDate(dateStr string) (time.Time, error) {
	dateStr = strings.TrimSpace(dateStr)
	// Remove timezone name in parentheses if present
	if idx := strings.Index(dateStr, " ("); idx > 0 {
		dateStr = dateStr[:idx]
	}
	return time.Parse("Mon, 2 Jan 2006 15:04:05 -0700", dateStr)
}

// writeHeadersInOrder writes headers in a consistent order
func writeHeadersInOrder(buf *bytes.Buffer, header textproto.MIMEHeader, config Config) {
	// Define the desired header order
	headerOrder := []string{"From", "To", "Subject", "Newsgroups", "X-Content"}
	
	for _, key := range headerOrder {
		// Skip From header in email mode
		if key == "From" && config.EmailMode {
			continue
		}
		
		// Use custom From header if provided, otherwise default
		if key == "From" && !config.EmailMode {
			fromValue := "Anonymous <anonymous@domain.tld>"
			if config.FromHeader != "" {
				fromValue = config.FromHeader
			}
			buf.WriteString(fmt.Sprintf("From: %s\r\n", fromValue))
			continue
		}
		
		if values, exists := header[key]; exists {
			for _, value := range values {
				buf.WriteString(fmt.Sprintf("%s: %s\r\n", key, value))
			}
		}
	}
}

// postArticle posts a single article to the NNTP server with consistent header order
func postArticle(conn net.Conn, article *Article, newsgroups string, config Config) error {
	reader := bufio.NewReader(conn)
	writer := bufio.NewWriter(conn)

	// Send POST command
	fmt.Fprintf(conn, "POST\r\n")
	response, err := reader.ReadString('\n')
	if err != nil {
		return fmt.Errorf("POST command failed: %v", err)
	}
	if !strings.HasPrefix(response, "340 ") {
		return fmt.Errorf("server refused article: %s", strings.TrimSpace(response))
	}

	// Build article with headers in consistent order
	var buf bytes.Buffer
	
	// Write headers in specific order
	writeHeadersInOrder(&buf, article.Header, config)
	
	// End of headers
	buf.WriteString("\r\n")
	
	// Write base64 encoded body with 76-character line breaks
	encoded := base64.StdEncoding.EncodeToString(article.Body)
	for i := 0; i < len(encoded); i += 76 {
		end := i + 76
		if end > len(encoded) {
			end = len(encoded)
		}
		buf.WriteString(encoded[i:end] + "\r\n")
	}
	
	// End of article marker
	buf.WriteString(".\r\n")

	// Send article
	if _, err := writer.Write(buf.Bytes()); err != nil {
		return fmt.Errorf("failed to write article: %v", err)
	}
	writer.Flush()

	// Check response
	response, err = reader.ReadString('\n')
	if err != nil {
		return fmt.Errorf("failed to read POST response: %v", err)
	}
	if !strings.HasPrefix(response, "240 ") {
		return fmt.Errorf("article posting failed: %s", strings.TrimSpace(response))
	}

	return nil
}

// fetchArticles retrieves articles from a newsgroup with improved caching
func fetchArticles(conn net.Conn, config Config) ([]*Article, error) {
	reader := bufio.NewReader(conn)

	// Select newsgroup
	fmt.Fprintf(conn, "GROUP %s\r\n", config.Newsgroups)
	response, err := reader.ReadString('\n')
	if err != nil {
		return nil, fmt.Errorf("group command failed: %v", err)
	}
	if !strings.HasPrefix(response, "211 ") {
		return nil, fmt.Errorf("group selection failed: %s", strings.TrimSpace(response))
	}

	// Parse group response
	parts := strings.Fields(response)
	if len(parts) < 4 {
		return nil, fmt.Errorf("invalid group response: %s", strings.TrimSpace(response))
	}

	first, err := strconv.Atoi(parts[2])
	if err != nil {
		return nil, fmt.Errorf("invalid first article: %v", err)
	}
	last, err := strconv.Atoi(parts[3])
	if err != nil {
		return nil, fmt.Errorf("invalid last article: %v", err)
	}

	var articles []*Article
	cutoff := time.Now().AddDate(0, 0, -config.Days)
	batchStart := first

	// Check if we should resume from last fetch
	stateMutex.RLock()
	saved, exists := state[config.Newsgroups]
	stateMutex.RUnlock()
	
	if config.Latest && exists {
		if saved.LastArticle >= last {
			fmt.Printf("No new articles available since last fetch (last article: %d)\n", saved.LastArticle)
			return articles, nil
		}
		if saved.LastArticle >= first && saved.LastArticle < last {
			batchStart = saved.LastArticle + 1
			fmt.Printf("Resuming from article %d (last fetched was %d)\n", batchStart, saved.LastArticle)
		}
	}

	// Create esub validator
	esubValidator := &Esub{key: config.Key}
	
	// Track processed esubs in this session to avoid duplicates
	processedEsubs := make(map[string]bool)
	
	// Track downloaded file parts to avoid downloading same part multiple times
	downloadedParts := make(map[string]bool) // key: "filename:total:hashPrefix"

	// Process articles in batches
	for batchStart <= last {
		batchEnd := batchStart + config.MaxBatch - 1
		if batchEnd > last {
			batchEnd = last
		}

		// Get overview of articles in batch
		fmt.Fprintf(conn, "XOVER %d-%d\r\n", batchStart, batchEnd)
		xoverHeader, err := reader.ReadString('\n')
		if err != nil {
			return nil, fmt.Errorf("xover header read failed: %v", err)
		}
		if !strings.HasPrefix(xoverHeader, "224 ") {
			return nil, fmt.Errorf("xover command failed: %s", strings.TrimSpace(xoverHeader))
		}

		// Read overview data and filter BEFORE downloading
		var articlesToFetch []string
		var articleSubjects []string
		
		for {
			line, err := reader.ReadString('\n')
			if err != nil {
				return nil, fmt.Errorf("xover read failed: %v", err)
			}
			if line == ".\r\n" {
				break
			}

			line = strings.TrimRight(line, "\r\n")
			fields := strings.Split(line, "\t")
			if len(fields) < 8 {
				continue
			}

			articleNum := fields[0]
			subject := fields[1]
			
			// Apply date filter if specified
			if config.Days > 0 {
				date, err := parseDate(fields[3])
				if err != nil || date.Before(cutoff) {
					continue
				}
			}
			
			// Skip if esub is already processed in this session
			if processedEsubs[subject] {
				continue
			}
			
			// Skip if esub is in replay cache
			if cache != nil && cache.HasReplay(subject) {
				continue
			}
			
			// Quick esub format check before downloading
			if len(subject) != 48 {
				continue // Not a valid esub format
			}
			
			articlesToFetch = append(articlesToFetch, articleNum)
			articleSubjects = append(articleSubjects, subject)
		}

		// Fetch individual articles
		for i, num := range articlesToFetch {
			subject := articleSubjects[i]
			
			// Mark as processed in this session
			processedEsubs[subject] = true
			
			article, err := fetchArticleWithCache(conn, reader, num, config.Key, subject, esubValidator, downloadedParts)
			if err != nil {
				fmt.Printf("Warning: %v\n", err)
				continue
			}
			if article != nil {
				articles = append(articles, article)
			}
		}

		// Update state
		if config.Latest && batchEnd > first {
			stateMutex.Lock()
			state[config.Newsgroups] = GroupState{
				LastArticle: batchEnd,
				LastFetch:   time.Now(),
			}
			stateMutex.Unlock()
			
			if err := saveState(config.Newsgroups); err != nil {
				fmt.Printf("Warning: failed to save state: %v\n", err)
			}
		}

		batchStart = batchEnd + 1
		
		// Save cache periodically
		if cache != nil && len(processedEsubs)%20 == 0 {
			if err := cache.Save(); err != nil {
				fmt.Printf("Warning: failed to save cache: %v\n", err)
			}
		}
	}
	
	// Final cache save
	if cache != nil {
		if err := cache.Save(); err != nil {
			fmt.Printf("Warning: failed to save cache: %v\n", err)
		}
	}

	return articles, nil
}

// calculateHash computes SHA3-256 hash of content
func calculateHash(content []byte) string {
	hash := sha3.Sum256(content)
	return hex.EncodeToString(hash[:])
}

// fetchArticleWithCache retrieves a single article with caching
func fetchArticleWithCache(conn net.Conn, reader *bufio.Reader, articleNum, key, subject string, 
	esubValidator *Esub, downloadedParts map[string]bool) (*Article, error) {
	
	// Validate esub BEFORE downloading article body
	if !esubValidator.Validate(subject) {
		return nil, nil // Skip invalid esub
	}

	// Request article
	fmt.Fprintf(conn, "ARTICLE %s\r\n", articleNum)
	response, err := reader.ReadString('\n')
	if err != nil {
		return nil, fmt.Errorf("failed to fetch article %s: %v", articleNum, err)
	}
	if !strings.HasPrefix(response, "220 ") {
		return nil, fmt.Errorf("article %s unavailable: %s", articleNum, strings.TrimSpace(response))
	}

	// Parse headers
	header := make(textproto.MIMEHeader)
	header.Set("Subject", subject) // Use the subject from XOVER
	
	for {
		line, err := reader.ReadString('\n')
		if err != nil {
			return nil, fmt.Errorf("error reading article %s: %v", articleNum, err)
		}
		line = strings.TrimRight(line, "\r\n")
		
		if line == "" {
			break // Empty line indicates end of headers
		}
		
		if idx := strings.Index(line, ":"); idx > 0 {
			key := strings.TrimSpace(line[:idx])
			value := strings.TrimSpace(line[idx+1:])
			header.Add(key, value)
		}
	}

	// Read body (base64 encoded)
	var body strings.Builder
	for {
		line, err := reader.ReadString('\n')
		if err != nil {
			return nil, fmt.Errorf("error reading article body %s: %v", articleNum, err)
		}
		line = strings.TrimRight(line, "\r\n")
		
		if line == "." {
			break // End of article
		}
		
		// Unescape lines starting with ".."
		if strings.HasPrefix(line, "..") {
			line = line[1:]
		}
		body.WriteString(line)
	}

	// Decode base64 body
	decoded, err := base64.StdEncoding.DecodeString(body.String())
	if err != nil {
		// Try with URL encoding if standard decoding fails
		decoded, err = base64.URLEncoding.DecodeString(body.String())
		if err != nil {
			fmt.Printf("Warning: failed to decode base64 for article %s: %v\n", articleNum, err)
			return nil, nil
		}
	}

	// Parse X-Content header for file information
	var part, total int
	var filename string
	xContent := header.Get("X-Content")
	if xContent != "" && strings.Contains(xContent, "Part [") {
		// Extract part info: "Part [1/31] bin"
		startIdx := strings.Index(xContent, "[")
		endIdx := strings.Index(xContent, "]")
		if startIdx != -1 && endIdx != -1 && endIdx > startIdx {
			partInfo := xContent[startIdx+1 : endIdx]
			parts := strings.Split(partInfo, "/")
			if len(parts) == 2 {
				part, _ = strconv.Atoi(strings.TrimSpace(parts[0]))
				total, _ = strconv.Atoi(strings.TrimSpace(parts[1]))
			}
			
			// Extract filename (after "] ")
			if endIdx+2 < len(xContent) {
				filename = strings.TrimSpace(xContent[endIdx+2:])
			}
		}
	}

	// Skip if we don't have complete information
	if filename == "" || part == 0 || total == 0 {
		fmt.Printf("Warning: incomplete X-Content header in article %s: %s\n", articleNum, xContent)
		return nil, nil
	}

	// Calculate content hash
	contentHash := calculateHash(decoded)
	
	// Create cache key for this file part
	partCacheKey := fmt.Sprintf("%s:%d:%s", filename, total, contentHash[:16])
	
	// Check if we've already downloaded this exact part in this session
	if downloadedParts[partCacheKey] {
		fmt.Printf("Skipping duplicate part %d/%d of %s (already downloaded this session)\n", 
			part, total, filename)
		return nil, nil
	}
	
	// Mark as downloaded in this session
	downloadedParts[partCacheKey] = true

	// Check file cache to avoid duplicates across sessions
	if cache != nil {
		if cache.HasFile(filename, part, contentHash) {
			fmt.Printf("Skipping cached part %d/%d of %s\n", part, total, filename)
			return nil, nil
		}
		
		// Add to file cache
		cache.AddFile(filename, part, total, subject, contentHash)
	}

	return &Article{
		Header:   header,
		Body:     decoded,
		Part:     part,
		Total:    total,
		Filename: filename,
		Number:   articleNum,
		Esub:     subject,
		Hash:     contentHash,
	}, nil
}

// splitFile splits a file into blocks of specified size (in KB)
func splitFile(filename string, blockSizeKB int) ([][]byte, error) {
	blockSize := blockSizeKB * 1024 // Convert KB to bytes
	file, err := os.Open(filename)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	var blocks [][]byte
	buffer := make([]byte, blockSize)

	for {
		n, err := file.Read(buffer)
		if err != nil && err != io.EOF {
			return nil, err
		}
		if n == 0 {
			break
		}

		block := make([]byte, n)
		copy(block, buffer[:n])
		blocks = append(blocks, block)
	}

	return blocks, nil
}

// createArticles creates Article objects from file blocks with proper header order
func createArticles(filename string, blocks [][]byte, config Config) ([]*Article, error) {
	var articles []*Article
	esub := &Esub{key: config.Key}
	
	totalParts := len(blocks)
	for i, block := range blocks {
		// Generate unique esub for each article
		subject, err := esub.Generate()
		if err != nil {
			return nil, fmt.Errorf("failed to generate esub for part %d: %v", i+1, err)
		}

		header := make(textproto.MIMEHeader)
		
		// Set headers in proper order (From/To first, X-Content last)
		
		// Add From header unless in email mode
		if !config.EmailMode {
			fromValue := "Anonymous <anonymous@domain.tld>"
			if config.FromHeader != "" {
				fromValue = config.FromHeader
			}
			header.Set("From", fromValue)
		}
		
		// Add recipient if specified (for email mode)
		if config.To != "" {
			header.Set("To", config.To)
		}
		
		// Required headers (standard order)
		header.Set("Subject", subject)
		header.Set("Newsgroups", config.Newsgroups)
		
		// X-Content header last (as per specification)
		header.Set("X-Content", fmt.Sprintf("Part [%d/%d] %s", i+1, totalParts, filename))

		// Calculate content hash
		contentHash := calculateHash(block)

		article := &Article{
			Header:   header,
			Body:     block,
			Part:     i + 1,
			Total:    totalParts,
			Filename: filename,
			Esub:     subject,
			Hash:     contentHash,
		}
		articles = append(articles, article)
	}

	return articles, nil
}

// sendArticles posts multiple articles to the NNTP server
func sendArticles(articles []*Article, config Config) error {
	proxyAddr := fmt.Sprintf("127.0.0.1:%d", config.ProxyPort)
	
	// Connect to NNTP server
	conn, err := dialNNTP(config.NNTP, config.UseTLS, proxyAddr)
	if err != nil {
		return fmt.Errorf("failed to connect to NNTP server: %v", err)
	}
	defer conn.Close()

	// Set read timeout
	if err := conn.SetReadDeadline(time.Now().Add(time.Duration(config.Timeout) * time.Second)); err != nil {
		fmt.Printf("Warning: couldn't set timeout: %v\n", err)
	}

	// Read server greeting
	reader := bufio.NewReader(conn)
	if _, err := reader.ReadString('\n'); err != nil {
		return fmt.Errorf("server greeting failed: %v", err)
	}

	// Authenticate if credentials provided
	if config.Username != "" {
		if err := authenticateNNTP(conn, config.Username, config.Password); err != nil {
			return fmt.Errorf("authentication failed: %v", err)
		}
	}

	// Post articles
	for i, article := range articles {
		if err := postArticle(conn, article, config.Newsgroups, config); err != nil {
			return fmt.Errorf("failed to post article %d: %v", i+1, err)
		}
		fmt.Printf("Posted article %d/%d for %s (esub: %s)\n", i+1, len(articles), article.Filename, article.Esub)
		time.Sleep(100 * time.Millisecond) // Small delay between posts
	}

	// Disconnect
	fmt.Fprintf(conn, "QUIT\r\n")
	return nil
}

// reconstructFile reconstructs original files from article parts
func reconstructFile(articles []*Article, outputDir string) error {
	if len(articles) == 0 {
		return errors.New("no articles to reconstruct")
	}

	// First, group by filename
	files := make(map[string]map[int][]*Article) // filename -> total -> articles
	
	for _, article := range articles {
		if article.Filename != "" && article.Part > 0 && article.Total > 0 {
			if files[article.Filename] == nil {
				files[article.Filename] = make(map[int][]*Article)
			}
			files[article.Filename][article.Total] = append(files[article.Filename][article.Total], article)
		}
	}
	
	// For each filename, find the most complete set
	for filename, totalMap := range files {
		fmt.Printf("\nProcessing file: %s\n", filename)
		fmt.Printf("Found %d different versions (different totals)\n", len(totalMap))
		
		// Find the best candidate (most complete set)
		var bestTotal int
		var bestArticles []*Article
		var bestCompleteness float64
		
		for total, articles := range totalMap {
			fmt.Printf("  Version with %d total parts: found %d articles\n", total, len(articles))
			
			// Count unique parts
			uniqueParts := make(map[int]bool)
			for _, article := range articles {
				uniqueParts[article.Part] = true
			}
			
			completeness := float64(len(uniqueParts)) / float64(total)
			fmt.Printf("    Completeness: %.1f%% (%d/%d)\n", completeness*100, len(uniqueParts), total)
			
			if completeness > bestCompleteness || 
			   (completeness == bestCompleteness && total > bestTotal) {
				bestTotal = total
				bestArticles = articles
				bestCompleteness = completeness
			}
		}
		
		if bestCompleteness == 0 {
			fmt.Printf("No usable articles for %s\n", filename)
			continue
		}
		
		// Reconstruct the best version
		if err := reconstructSingleFile(filename, bestTotal, bestArticles, outputDir); err != nil {
			fmt.Printf("Error reconstructing %s: %v\n", filename, err)
		}
	}
	
	return nil
}

// reconstructSingleFile reconstructs a single file from its articles
func reconstructSingleFile(filename string, total int, articles []*Article, outputDir string) error {
	// Remove duplicates (keep first occurrence of each part)
	partMap := make(map[int]*Article)
	for _, article := range articles {
		if _, exists := partMap[article.Part]; !exists {
			partMap[article.Part] = article
		} else {
			fmt.Printf("  Duplicate part %d, keeping first\n", article.Part)
		}
	}
	
	// Create sorted list of parts
	var sortedArticles []*Article
	for i := 1; i <= total; i++ {
		if article, exists := partMap[i]; exists {
			sortedArticles = append(sortedArticles, article)
		}
	}
	
	// Sort just to be sure
	sort.Slice(sortedArticles, func(i, j int) bool {
		return sortedArticles[i].Part < sortedArticles[j].Part
	})
	
	// Check completeness
	if len(sortedArticles) != total {
		fmt.Printf("  Warning: incomplete file (%d/%d parts)\n", len(sortedArticles), total)
		fmt.Printf("  Missing parts: ")
		for i := 1; i <= total; i++ {
			if _, exists := partMap[i]; !exists {
				fmt.Printf("%d ", i)
			}
		}
		fmt.Println()
		
		// Create incomplete filename
		filename = fmt.Sprintf("%s_INCOMPLETE_%dof%d", filename, len(sortedArticles), total)
	}
	
	// Reconstruct file
	outputPath := filepath.Join(outputDir, filename)
	file, err := os.Create(outputPath)
	if err != nil {
		return fmt.Errorf("failed to create file: %v", err)
	}
	defer file.Close()
	
	for _, article := range sortedArticles {
		if _, err := file.Write(article.Body); err != nil {
			return fmt.Errorf("failed to write part %d: %v", article.Part, err)
		}
	}
	
	fmt.Printf("  Reconstructed: %s (%d parts)\n", outputPath, len(sortedArticles))
	return nil
}

// saveManifest creates a manifest file for easy reconstruction
func saveManifest(files []string, blockSizeKB int, totalArticles int) {
	var manifest []ManifestEntry
	articleCounter := 1
	
	for _, filename := range files {
		// Read file to determine size and calculate parts
		fileInfo, err := os.Stat(filename)
		if err != nil {
			continue
		}
		
		fileSizeKB := fileInfo.Size() / 1024
		estimatedParts := int(fileSizeKB) / blockSizeKB
		if int(fileSizeKB)%blockSizeKB != 0 {
			estimatedParts++
		}
		
		// Create manifest entries for this file
		for part := 1; part <= estimatedParts; part++ {
			articleFile := fmt.Sprintf("%04d.txt", articleCounter)
			manifest = append(manifest, ManifestEntry{
				ArticleFile:  articleFile,
				OriginalFile: filepath.Base(filename),
				PartNumber:   part,
				TotalParts:   estimatedParts,
				Esub:         fmt.Sprintf("generated_for_%s_part_%d", filepath.Base(filename), part),
				BlockSizeKB:  blockSizeKB,
			})
			articleCounter++
		}
	}
	
	// Save manifest as JSON
	manifestData, err := json.MarshalIndent(manifest, "", "  ")
	if err != nil {
		fmt.Printf("Warning: failed to create manifest: %v\n", err)
		return
	}
	
	if err := os.WriteFile("manifest.json", manifestData, 0644); err != nil {
		fmt.Printf("Warning: failed to save manifest: %v\n", err)
	} else {
		fmt.Printf("\nManifest saved: manifest.json (%d entries)\n", len(manifest))
	}
	
	// Also save a simple README
	saveReadme(totalArticles, blockSizeKB)
}

// saveReadme creates a README file with instructions
func saveReadme(totalArticles int, blockSizeKB int) {
	readme := fmt.Sprintf(`Usenet Articles Manifest

Summary:
- Total articles: %d
- Block size: %d KB
- Date: %s

Files:
- *.txt: Individual Usenet articles (0001.txt, 0002.txt, etc.)
- manifest.json: Reconstruction information
- README.md: This file

To send articles to Usenet:
1. Use the program in send mode:
   b4u -s -k "your-key" -n "newsgroup" -S "server:port" *.txt

2. Or send individually:
   b4u -s -k "your-key" -n "newsgroup" -S "server:port" 0001.txt
   b4u -s -k "your-key" -n "newsgroup" -S "server:port" 0002.txt
   ... etc.

To reconstruct original files from Usenet:
b4u -r -k "your-key" -n "newsgroup" -S "server:port"

Article format:
Each .txt file contains:
- Headers (From, Subject, Newsgroups, X-Content)
- Base64 encoded binary data (76 chars per line)
- Ending with a single dot on its own line

Notes:
- Articles are sequentially numbered: 0001.txt, 0002.txt, etc.
- The manifest.json file contains mapping back to original files
- Use -rc flag to enable cache and avoid duplicate downloads
`, totalArticles, blockSizeKB, time.Now().Format("2006-01-02 15:04:05"))

	if err := os.WriteFile("README.txt", []byte(readme), 0644); err != nil {
		fmt.Printf("Warning: failed to save README: %v\n", err)
	} else {
		fmt.Println("README saved: README.txt")
	}
}

// printUsage displays program usage information
func printUsage() {
	fmt.Println("b4u - Usenet Binary File Transfer Tool")
	fmt.Println("")
	fmt.Println("Usage:")
	fmt.Println("  Send mode:    b4u -s -k <key> -n <newsgroups> -S <server:port> <file1> <file2> ...")
	fmt.Println("  Receive mode: b4u -r -k <key> -n <newsgroups> -S <server:port>")
	fmt.Println("  Save mode:    b4u -k <key> <file1> <file2> ...")
	fmt.Println("")
	fmt.Println("Required Options:")
	fmt.Println("  -k string        esub key password (required for all modes)")
	fmt.Println("  -n string        Newsgroups (comma separated, required for send/receive)")
	fmt.Println("  -S string        NNTP server:port (required for send/receive)")
	fmt.Println("")
	fmt.Println("Mode Selection:")
	fmt.Println("  -s               Send all files to newsgroup")
	fmt.Println("  -r               Receive all files from specified newsgroup")
	fmt.Println("  (no -s or -r)    Save articles locally without sending (creates 0001.txt, 0002.txt, etc.)")
	fmt.Println("")
	fmt.Println("File Options:")
	fmt.Println("  -b int           Block size in KB (default: 64, max recommended: 256)")
	fmt.Println("  -e               Mixmaster email mode (omits From: header)")
	fmt.Println("  -f string        Custom From: header (default: Anonymous <anonymous@domain.tld>)")
	fmt.Println("  -t string        To: address (for Mixmaster email mode)")
	fmt.Println("")
	fmt.Println("NNTP Options:")
	fmt.Println("  -u string        NNTP username")
	fmt.Println("  -p string        NNTP password")
	fmt.Println("  -tls             Use TLS connection")
	fmt.Println("  -days int        Download articles from last N days (0 for all, default: 1)")
	fmt.Println("  -latest          Only fetch articles newer than last run")
	fmt.Println("  -batch int       Maximum batch size for XOVER command (default: 500)")
	fmt.Println("  -timeout int     Read timeout in seconds (default: 1200)")
	fmt.Println("")
	fmt.Println("Proxy Options:")
	fmt.Println("  -pp int          SOCKS5 proxy port (default: 9050 for Tor)")
	fmt.Println("")
	fmt.Println("Cache Options:")
	fmt.Println("  -rc              Enable replay cache and file cache")
	fmt.Println("  -dbpath string   Custom path for cache JSON file")
	fmt.Println("")
	fmt.Println("Examples:")
	fmt.Println("  Send file:    b4u -s -k \"my-password\" -n alt.test -S news.server.com:119 file.zip")
	fmt.Println("  Receive:      b4u -r -k \"my-password\" -n alt.test -S news.server.com:119")
	fmt.Println("  Save locally: b4u -k \"my-password\" file.zip (creates 0001.txt, 0002.txt, etc.)")
	fmt.Println("  Tor Browser:  b4u -r -k \"my-password\" -n alt.test -S news.server.com:119 -pp 9150")
	fmt.Println("  With cache:   b4u -r -k \"my-password\" -n alt.test -S news.server.com:119 -rc")
	fmt.Println("  Large files:  b4u -s -k \"my-password\" -n alt.test -S news.server.com:119 -b 256 large.zip")
	fmt.Println("  Custom From:  b4u -s -k \"my-password\" -n alt.test -S news.server.com:119 -f \"John Doe <john@example.com>\" file.zip")
	fmt.Println("  Email mode:   b4u -k \"my-password\" -n alt.test -e -t \"recipient@example.com\" file.zip")
}

func main() {
	// Parse command line arguments
	key := flag.String("k", "", "esub key password")
	to := flag.String("t", "", "To: address (for email)")
	fromHeader := flag.String("f", "", "Custom From: header (default: Anonymous <anonymous@domain.tld>)")
	newsgroups := flag.String("n", "", "Newsgroups (comma separated)")
	blockSize := flag.Int("b", 64, "Block size in KB (default 64)")
	sendFlag := flag.Bool("s", false, "Send all files")
	receiveFlag := flag.Bool("r", false, "Receive all files from specified newsgroup")
	nntpServer := flag.String("S", "", "NNTP server:port")
	proxyPort := flag.Int("pp", 9050, "Proxy port")
	emailMode := flag.Bool("e", false, "Email mode (no From: header)")
	username := flag.String("u", "", "NNTP username")
	password := flag.String("p", "", "NNTP password")
	useTLS := flag.Bool("tls", false, "Use TLS connection")
	days := flag.Int("days", 1, "Download articles from last N days (0 for all)")
	latest := flag.Bool("latest", false, "Only fetch articles newer than last run")
	maxBatch := flag.Int("batch", 500, "Maximum batch size for XOVER command")
	timeout := flag.Int("timeout", 1200, "Read timeout in seconds")
	
	flag.Usage = printUsage
	flag.Parse()
	
	// Show usage if no arguments
	if len(os.Args) == 1 {
		printUsage()
		os.Exit(0)
	}
	
	// Validate required parameters
	if *key == "" {
		fmt.Println("Error: esub key (-k) is required")
		printUsage()
		os.Exit(1)
	}
	
	// Create configuration
	config := Config{
		Key:        *key,
		To:         *to,
		FromHeader: *fromHeader,
		Newsgroups: *newsgroups,
		BlockSize:  *blockSize,
		Send:       *sendFlag,
		Receive:    *receiveFlag,
		NNTP:       *nntpServer,
		ProxyPort:  *proxyPort,
		EmailMode:  *emailMode,
		Username:   *username,
		Password:   *password,
		UseTLS:     *useTLS,
		Days:       *days,
		Latest:     *latest,
		MaxBatch:   *maxBatch,
		Timeout:    *timeout,
	}
	
	// Initialize cache (JSON-based)
	if *rcFlag {
		fmt.Println("Cache enabled")
		if err := initCache(); err != nil {
			fmt.Printf("Warning: cache initialization failed: %v\n", err)
			fmt.Println("Continuing without cache...")
		} else {
			fmt.Printf("Cache loaded from: %s\n", cache.filePath)
			fmt.Printf("Replay cache entries: %d\n", len(cache.ReplayCache))
			fmt.Printf("File cache entries: %d\n", len(cache.FileCache))
		}
	}
	
	// Save cache on exit
	defer func() {
		if cache != nil {
			if err := cache.Save(); err != nil {
				fmt.Printf("Warning: failed to save cache: %v\n", err)
			}
		}
	}()
	
	// Handle send mode
	if config.Send {
		if config.Newsgroups == "" {
			fmt.Println("Error: newsgroups (-n) required for send mode")
			printUsage()
			os.Exit(1)
		}
		if config.NNTP == "" {
			fmt.Println("Error: NNTP server (-S) required for send mode")
			printUsage()
			os.Exit(1)
		}
		
		files := flag.Args()
		if len(files) == 0 {
			fmt.Println("Error: no files specified for sending")
			printUsage()
			os.Exit(1)
		}
		
		for _, filename := range files {
			// Split file into blocks
			blocks, err := splitFile(filename, config.BlockSize)
			if err != nil {
				fmt.Printf("Error splitting file %s: %v\n", filename, err)
				continue
			}
			
			fmt.Printf("Split %s into %d blocks of %d KB each\n", filename, len(blocks), config.BlockSize)
			
			// Create articles from blocks
			articles, err := createArticles(filepath.Base(filename), blocks, config)
			if err != nil {
				fmt.Printf("Error creating articles for %s: %v\n", filename, err)
				continue
			}
			
			// Send articles to NNTP server
			err = sendArticles(articles, config)
			if err != nil {
				fmt.Printf("Error sending articles for %s: %v\n", filename, err)
			} else {
				fmt.Printf("Successfully sent %d articles for %s\n", len(articles), filename)
			}
		}
	} else if config.Receive {
		// Handle receive mode
		if config.Newsgroups == "" {
			fmt.Println("Error: newsgroups (-n) required for receive mode")
			printUsage()
			os.Exit(1)
		}
		if config.NNTP == "" {
			fmt.Println("Error: NNTP server (-S) required for receive mode")
			printUsage()
			os.Exit(1)
		}
		
		// Load previous state for this newsgroup
		if err := loadState(config.Newsgroups); err != nil {
			fmt.Printf("Warning: failed to load state: %v\n", err)
		}
		
		// Connect to NNTP server
		proxyAddr := fmt.Sprintf("127.0.0.1:%d", config.ProxyPort)
		conn, err := dialNNTP(config.NNTP, config.UseTLS, proxyAddr)
		if err != nil {
			fmt.Printf("Connection failed: %v\n", err)
			os.Exit(1)
		}
		defer conn.Close()
		
		// Set timeout
		if err := conn.SetReadDeadline(time.Now().Add(time.Duration(config.Timeout) * time.Second)); err != nil {
			fmt.Printf("Warning: couldn't set timeout: %v\n", err)
		}
		
		// Read server greeting
		reader := bufio.NewReader(conn)
		if _, err := reader.ReadString('\n'); err != nil {
			fmt.Printf("Server greeting failed: %v\n", err)
			os.Exit(1)
		}
		
		// Authenticate if credentials provided
		if config.Username != "" {
			if err := authenticateNNTP(conn, config.Username, config.Password); err != nil {
				fmt.Printf("Authentication failed: %v\n", err)
				os.Exit(1)
			}
		}
		
		// Fetch articles
		articles, err := fetchArticles(conn, config)
		if err != nil {
			fmt.Printf("Error fetching articles: %v\n", err)
			os.Exit(1)
		}
		
		// Reconstruct files from articles
		if len(articles) > 0 {
			if err := reconstructFile(articles, "."); err != nil {
				fmt.Printf("Error reconstructing files: %v\n", err)
			}
		} else {
			fmt.Println("No valid articles found")
		}
		
		// Disconnect
		fmt.Fprintf(conn, "QUIT\r\n")
	} else {
		// Save mode (create articles locally without sending)
		files := flag.Args()
		if len(files) == 0 {
			fmt.Println("Error: no files specified")
			printUsage()
			os.Exit(1)
		}
		
		// Track total number of articles for manifest
		totalArticles := 0
		allArticlesInfo := make([]struct {
			filename string
			parts    int
		}, 0)
		
		for _, filename := range files {
			// Split file into blocks
			blocks, err := splitFile(filename, config.BlockSize)
			if err != nil {
				fmt.Printf("Error splitting file %s: %v\n", filename, err)
				continue
			}
			
			fmt.Printf("Split %s into %d blocks of %d KB each\n", filename, len(blocks), config.BlockSize)
			
			// Create articles from blocks
			articles, err := createArticles(filepath.Base(filename), blocks, config)
			if err != nil {
				fmt.Printf("Error creating articles for %s: %v\n", filename, err)
				continue
			}
			
			// Track article info for manifest
			allArticlesInfo = append(allArticlesInfo, struct {
				filename string
				parts    int
			}{
				filename: filepath.Base(filename),
				parts:    len(articles),
			})
			
			// Save articles locally with sequential numbering
			for i, article := range articles {
				// Create sequential filename: 0001.txt, 0002.txt, etc.
				articleNumber := totalArticles + i + 1
				articleFile := fmt.Sprintf("%04d.txt", articleNumber)
				
				var buf bytes.Buffer
				// Write headers in consistent order
				writeHeadersInOrder(&buf, article.Header, config)
				
				buf.WriteString("\r\n")
				
				// Write base64 encoded body with line breaks
				encoded := base64.StdEncoding.EncodeToString(article.Body)
				for i := 0; i < len(encoded); i += 76 {
					end := i + 76
					if end > len(encoded) {
						end = len(encoded)
					}
					buf.WriteString(encoded[i:end] + "\r\n")
				}
				
				// End of article marker
				buf.WriteString(".\r\n")
				
				// Save to file
				err := os.WriteFile(articleFile, buf.Bytes(), 0644)
				if err != nil {
					fmt.Printf("Error saving article %s: %v\n", articleFile, err)
				} else {
					fmt.Printf("Saved article: %s (original: %s part %d/%d)\n", 
						articleFile, article.Filename, article.Part, article.Total)
				}
			}
			
			totalArticles += len(articles)
		}
		
		// Save manifest and README if we saved any articles
		if totalArticles > 0 {
			fmt.Printf("\nTotal articles saved: %d\n", totalArticles)
			fmt.Println("Files created: 0001.txt, 0002.txt, ...")
			
			saveManifest(files, config.BlockSize, totalArticles)
			
			// Show summary
			fmt.Println("\nSummary of created files:")
			for _, info := range allArticlesInfo {
				fmt.Printf("  %s: %d parts\n", info.filename, info.parts)
			}
			fmt.Printf("\nTo send all articles to Usenet:\n")
			fmt.Printf("  b4u -s -k \"%s\" -n \"newsgroup\" -S \"server:port\" *.txt\n", config.Key)
		}
	}
}
