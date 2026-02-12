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

// Cache stores replay and file cache for duplicate detection
type Cache struct {
	ReplayCache map[string]time.Time   // esub -> timestamp
	FileCache   map[string][]FileCacheEntry // filename:total -> []parts
	filePath    string
	mu          sync.RWMutex
}

// FileCacheEntry stores information about downloaded file parts
type FileCacheEntry struct {
	Part        int       `json:"part"`
	Total       int       `json:"total"`
	Esub        string    `json:"esub"`
	ContentHash string    `json:"content_hash"`
	Downloaded  time.Time `json:"downloaded"`
}

// GroupState stores progress per newsgroup
type GroupState struct {
	LastArticle int       `json:"last_article"`
	LastFetch   time.Time `json:"last_fetch"`
}

// Esub handles esub encryption/validation
type Esub struct {
	key string
}

// Article represents a Usenet article
type Article struct {
	Header   textproto.MIMEHeader
	Body     []byte
	Part     int
	Total    int
	Filename string
	Number   string
	Esub     string
	Hash     string
}

// ManifestEntry for manifest file
type ManifestEntry struct {
	ArticleFile  string `json:"article_file"`
	OriginalFile string `json:"original_file"`
	PartNumber   int    `json:"part_number"`
	TotalParts   int    `json:"total_parts"`
	Esub         string `json:"esub"`
	BlockSizeKB  int    `json:"block_size_kb"`
}

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
	ProxyPort  int    // SOCKS5 proxy port (0 = no proxy)
	EmailMode  bool   // Email mode (no From: header)
	UseTLS     bool   // Use STARTTLS for NNTP connection
	Days       int    // Download articles from last N days
	Latest     int    // Download only last N articles (0 = all)
	MaxBatch   int    // Maximum batch size for XOVER command
	Timeout    int    // Read timeout in seconds
	Verbose    bool   // Verbose output mode
}

// Global variables
var (
	rcFlag    = flag.Bool("rc", false, "enable replay cache")
	dbPath    = flag.String("dbpath", "", "custom path for replay cache database")
	cache     *Cache
	state     = make(map[string]GroupState) // Newsgroup state
	stateMutex sync.RWMutex                 // Mutex for state
)

// NewCache creates a new cache
func NewCache(path string) (*Cache, error) {
	c := &Cache{
		ReplayCache: make(map[string]time.Time),
		FileCache:   make(map[string][]FileCacheEntry),
		filePath:    path,
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
	var loaded struct {
		ReplayCache map[string]time.Time
		FileCache   map[string][]FileCacheEntry
	}
	if err := json.Unmarshal(data, &loaded); err != nil {
		return err
	}
	c.ReplayCache = loaded.ReplayCache
	c.FileCache = loaded.FileCache
	return nil
}

// Save saves cache to disk
func (c *Cache) Save() error {
	c.mu.RLock()
	data := struct {
		ReplayCache map[string]time.Time
		FileCache   map[string][]FileCacheEntry
	}{
		ReplayCache: c.ReplayCache,
		FileCache:   c.FileCache,
	}
	c.mu.RUnlock()
	jsonData, err := json.MarshalIndent(data, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(c.filePath, jsonData, 0600)
}

// AddReplay adds an esub to replay cache
func (c *Cache) AddReplay(esub string) {
	if c == nil {
		return
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	c.ReplayCache[esub] = time.Now()
}

// HasReplay checks if an esub exists in cache
func (c *Cache) HasReplay(esub string) bool {
	if c == nil {
		return false
	}
	c.mu.RLock()
	defer c.mu.RUnlock()
	_, exists := c.ReplayCache[esub]
	return exists
}

// AddFile adds a file part to file cache
func (c *Cache) AddFile(filename string, part, total int, esub, contentHash string) {
	if c == nil {
		return
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	key := fmt.Sprintf("%s:%d", filename, total)
	c.FileCache[key] = append(c.FileCache[key], FileCacheEntry{
		Part:        part,
		Total:       total,
		Esub:        esub,
		ContentHash: contentHash,
		Downloaded:  time.Now(),
	})
}

// HasFile checks if a file part has already been downloaded
func (c *Cache) HasFile(filename string, part, total int, contentHash string) bool {
	if c == nil {
		return false
	}
	c.mu.RLock()
	defer c.mu.RUnlock()
	key := fmt.Sprintf("%s:%d", filename, total)
	for _, entry := range c.FileCache[key] {
		if entry.Part == part && entry.ContentHash == contentHash {
			return true
		}
	}
	return false
}

// Cleanup removes old cache entries (>30 days)
func (c *Cache) Cleanup() {
	if c == nil {
		return
	}
	c.mu.Lock()
	defer c.mu.Unlock()
	cutoff := time.Now().AddDate(0, 0, -30)
	// Clean replay cache
	for esub, timestamp := range c.ReplayCache {
		if timestamp.Before(cutoff) {
			delete(c.ReplayCache, esub)
		}
	}
	// Clean file cache
	for key, entries := range c.FileCache {
		var kept []FileCacheEntry
		for _, entry := range entries {
			if entry.Downloaded.After(cutoff) {
				kept = append(kept, entry)
			}
		}
		if len(kept) == 0 {
			delete(c.FileCache, key)
		} else {
			c.FileCache[key] = kept
		}
	}
}

// deriveKey generates encryption key from password using Argon2
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
	nonce := make([]byte, 12)
	if _, err := rand.Read(nonce); err != nil {
		return "", fmt.Errorf("failed to generate nonce: %v", err)
	}
	key := e.deriveKey()
	cipher, err := chacha20.NewUnauthenticatedCipher(key, nonce)
	if err != nil {
		return "", fmt.Errorf("failed to create cipher: %v", err)
	}
	textHash := sha3.Sum256([]byte("text"))
	ciphertext := make([]byte, 12)
	cipher.XORKeyStream(ciphertext, textHash[:12])
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
	esubeBytes, err := hex.DecodeString(subject)
	if err != nil || len(esubeBytes) != 24 {
		return false
	}
	// Split into nonce and ciphertext
	nonce := esubeBytes[:12]
	receivedCiphertext := esubeBytes[12:]
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

// Helper functions for verbose output
func verbosePrintf(config Config, format string, args ...interface{}) {
	if config.Verbose {
		fmt.Printf(format, args...)
	}
}

func verbosePrintln(config Config, args ...interface{}) {
	if config.Verbose {
		fmt.Println(args...)
	}
}

// Progress bar function
func showProgress(current, total int, config Config) {
	if !config.Verbose || total == 0 {
		return
	}
	barWidth := 50
	progress := float64(current) / float64(total)
	filled := int(progress * float64(barWidth))
	bar := strings.Repeat("█", filled) + strings.Repeat("░", barWidth-filled)
	percent := int(progress * 100)
	fmt.Printf("\r[%s] %d/%d (%d%%)", bar, current, total, percent)
	if current >= total {
		fmt.Println()
	}
}

// dialNNTP establishes connection to NNTP server with STARTTLS support
func dialNNTP(server string, useTLS bool, proxyPort int) (net.Conn, error) {
	if proxyPort == 0 {
		return dialDirect(server, useTLS)
	}
	proxyAddr := fmt.Sprintf("127.0.0.1:%d", proxyPort)
	return dialWithProxy(server, useTLS, proxyAddr)
}

func dialDirect(server string, useTLS bool) (net.Conn, error) {
	address := server
	if !strings.Contains(server, ":") {
		address = fmt.Sprintf("%s:119", server)
	}
	conn, err := net.Dial("tcp", address)
	if err != nil {
		return nil, err
	}
	if useTLS {
		reader := bufio.NewReader(conn)
		fmt.Fprintf(conn, "STARTTLS\r\n")
		response, err := reader.ReadString('\n')
		if err != nil {
			conn.Close()
			return nil, fmt.Errorf("STARTTLS failed: %v", err)
		}
		if !strings.HasPrefix(response, "382 ") {
			conn.Close()
			return nil, fmt.Errorf("STARTTLS not supported: %s", strings.TrimSpace(response))
		}
		tlsConfig := &tls.Config{
			InsecureSkipVerify: true,
			ServerName:         strings.Split(server, ":")[0],
			MinVersion:         tls.VersionTLS12,
		}
		tlsConn := tls.Client(conn, tlsConfig)
		if err := tlsConn.Handshake(); err != nil {
			conn.Close()
			return nil, fmt.Errorf("TLS handshake failed: %v", err)
		}
		return tlsConn, nil
	}
	return conn, nil
}

func dialWithProxy(server string, useTLS bool, proxyAddr string) (net.Conn, error) {
	address := server
	if !strings.Contains(server, ":") {
		address = fmt.Sprintf("%s:119", server)
	}
	dialer, err := proxy.SOCKS5("tcp", proxyAddr, nil, proxy.Direct)
	if err != nil {
		return nil, fmt.Errorf("proxy connection failed: %v", err)
	}
	conn, err := dialer.Dial("tcp", address)
	if err != nil {
		return nil, fmt.Errorf("proxy dial failed: %v", err)
	}
	if useTLS {
		reader := bufio.NewReader(conn)
		fmt.Fprintf(conn, "STARTTLS\r\n")
		response, err := reader.ReadString('\n')
		if err != nil {
			conn.Close()
			return nil, fmt.Errorf("STARTTLS failed: %v", err)
		}
		if !strings.HasPrefix(response, "382 ") {
			conn.Close()
			return nil, fmt.Errorf("STARTTLS not supported: %s", strings.TrimSpace(response))
		}
		tlsConfig := &tls.Config{
			InsecureSkipVerify: true,
			ServerName:         strings.Split(server, ":")[0],
			MinVersion:         tls.VersionTLS12,
		}
		tlsConn := tls.Client(conn, tlsConfig)
		if err := tlsConn.Handshake(); err != nil {
			conn.Close()
			return nil, fmt.Errorf("TLS handshake failed: %v", err)
		}
		return tlsConn, nil
	}
	return conn, nil
}

// parseDate parses NNTP date strings with multiple format fallbacks
func parseDate(dateStr string) (time.Time, error) {
	// Clean up the string: remove extra spaces and timezone names in parentheses
	dateStr = strings.TrimSpace(dateStr)
	if idx := strings.Index(dateStr, " ("); idx > 0 {
		dateStr = dateStr[:idx]
	}
	dateStr = strings.TrimSpace(dateStr)

	// Common NNTP date formats (in order of likelihood)
	formats := []string{
		"Mon, 2 Jan 2006 15:04:05 -0700",   // RFC822 with numeric TZ
		"Mon, 2 Jan 2006 15:04:05 MST",     // RFC822 with named TZ
		"Mon, 2 Jan 2006 15:04:05 GMT",     // RFC822 GMT
		"2 Jan 2006 15:04:05 -0700",        // Without weekday
		"2 Jan 2006 15:04:05 MST",          // Without weekday, named TZ
		"2 Jan 2006 15:04:05 GMT",          // Without weekday, GMT
		"Mon, 02 Jan 2006 15:04:05 -0700",  // Zero-padded day
		"Mon, 02 Jan 2006 15:04:05 MST",
		"Mon, 02 Jan 2006 15:04:05 GMT",
		"02 Jan 2006 15:04:05 -0700",
		"02 Jan 2006 15:04:05 MST",
		"02 Jan 2006 15:04:05 GMT",
		"2006-01-02 15:04:05",              // ISO-like (some servers)
		"2006/01/02 15:04:05",              // Alternative separator
	}

	var lastErr error
	for _, format := range formats {
		t, err := time.Parse(format, dateStr)
		if err == nil {
			return t, nil
		}
		lastErr = err
	}

	// Final fallback: try to extract just the date part and ignore time/timezone
	// This is a last resort to avoid filtering out all articles
	parts := strings.Fields(dateStr)
	if len(parts) >= 3 {
		// Try parsing just "2 Jan 2006" portion
		shortDate := fmt.Sprintf("%s %s %s", parts[0], parts[1], parts[2])
		t, err := time.Parse("2 Jan 2006", shortDate)
		if err == nil {
			return t, nil
		}
	}

	return time.Time{}, fmt.Errorf("unable to parse date '%s': %v", dateStr, lastErr)
}

// writeHeadersInOrder writes headers in consistent order
func writeHeadersInOrder(buf *bytes.Buffer, header textproto.MIMEHeader, config Config) {
	headerOrder := []string{"From", "To", "Subject", "Newsgroups", "X-Content"}
	for _, key := range headerOrder {
		if key == "From" && config.EmailMode {
			continue
		}
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

// postArticle posts a single article to NNTP server
func postArticle(conn net.Conn, article *Article, newsgroups string, config Config) error {
	reader := bufio.NewReader(conn)
	writer := bufio.NewWriter(conn)
	fmt.Fprintf(conn, "POST\r\n")
	response, err := reader.ReadString('\n')
	if err != nil {
		return fmt.Errorf("POST command failed: %v", err)
	}
	if !strings.HasPrefix(response, "340 ") {
		return fmt.Errorf("server refused article: %s", strings.TrimSpace(response))
	}
	var buf bytes.Buffer
	writeHeadersInOrder(&buf, article.Header, config)
	buf.WriteString("\r\n")
	encoded := base64.StdEncoding.EncodeToString(article.Body)
	for i := 0; i < len(encoded); i += 76 {
		end := i + 76
		if end > len(encoded) {
			end = len(encoded)
		}
		buf.WriteString(encoded[i:end] + "\r\n")
	}
	buf.WriteString(".\r\n")
	if _, err := writer.Write(buf.Bytes()); err != nil {
		return fmt.Errorf("failed to write article: %v", err)
	}
	writer.Flush()
	response, err = reader.ReadString('\n')
	if err != nil {
		return fmt.Errorf("failed to read POST response: %v", err)
	}
	if !strings.HasPrefix(response, "240 ") {
		return fmt.Errorf("article posting failed: %s", strings.TrimSpace(response))
	}
	return nil
}

// fetchArticles retrieves articles from a newsgroup
func fetchArticles(conn net.Conn, config Config, resume bool) ([]*Article, error) {
	reader := bufio.NewReader(conn)
	fmt.Fprintf(conn, "GROUP %s\r\n", config.Newsgroups)
	response, err := reader.ReadString('\n')
	if err != nil {
		return nil, fmt.Errorf("group command failed: %v", err)
	}
	if !strings.HasPrefix(response, "211 ") {
		return nil, fmt.Errorf("group selection failed: %s", strings.TrimSpace(response))
	}
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
	batchStart := first

	// Priority 1: -latest N takes precedence (ignores resume/state)
	if config.Latest > 0 {
		newStart := last - config.Latest + 1
		if newStart > first {
			batchStart = newStart
			fmt.Printf("Fetching last %d articles by number (range: %d-%d)\n",
				config.Latest, batchStart, last)
		} else {
			fmt.Printf("Server has only %d articles total (requested last %d)\n",
				last-first+1, config.Latest)
			batchStart = first
		}
	} else if resume {
		// Priority 2: Resume mode (only when -latest 0)
		stateMutex.RLock()
		saved, exists := state[config.Newsgroups]
		stateMutex.RUnlock()
		if exists {
			if saved.LastArticle >= last {
				fmt.Printf("No new articles since last fetch (server high-water: %d, last fetched: %d)\n",
					last, saved.LastArticle)
				return articles, nil
			}
			if saved.LastArticle >= first {
				batchStart = saved.LastArticle + 1
				fmt.Printf("Resuming download from article %d\n", batchStart)
			}
		} else {
			fmt.Println("Warning: -resume specified but no previous state found – starting from beginning")
		}
	}

	// Show download range
	totalInRange := last - batchStart + 1
	if config.Verbose {
		fmt.Printf("Downloading articles %d-%d (%d total)\n", batchStart, last, totalInRange)
		fmt.Printf("Batch size: %d articles\n", config.MaxBatch)
		if config.Latest > 0 {
			fmt.Println("Mode: latest-N (ignores previous state)")
		} else if resume {
			fmt.Println("Mode: resume (continuing from last fetch)")
		} else {
			fmt.Println("Mode: full download (from article 1)")
		}
	}

	esubeValidator := &Esub{key: config.Key}
	processedEsubs := make(map[string]bool)
	downloadedParts := make(map[string]bool)
	articlesFound := 0
	articlesDownloaded := 0
	startTime := time.Now()

	for batchStart <= last {
		batchEnd := batchStart + config.MaxBatch - 1
		if batchEnd > last {
			batchEnd = last
		}

		// Show progress every 10k articles
		if config.Verbose && (batchStart-first)%10000 == 0 && batchStart > first {
			elapsed := time.Since(startTime).Seconds()
			percent := float64(batchStart-first) / float64(totalInRange) * 100
			fmt.Printf("Progress: %d/%d articles (%.1f%%) in %.1fs\n",
				batchStart-first, totalInRange, percent, elapsed)
		}

		// Get article overview
		fmt.Fprintf(conn, "XOVER %d-%d\r\n", batchStart, batchEnd)
		xoverHeader, err := reader.ReadString('\n')
		if err != nil {
			return nil, fmt.Errorf("xover header read failed: %v", err)
		}
		if !strings.HasPrefix(xoverHeader, "224 ") {
			return nil, fmt.Errorf("xover command failed: %s", strings.TrimSpace(xoverHeader))
		}

		var articlesToFetch []string
		var articleSubjects []string

		// Parse XOVER response
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
				continue // Skip malformed lines
			}

			articleNum := fields[0]
			subject := fields[1]

			// Skip non-esub subjects early (must be 48 hex chars = 24 bytes)
			if len(subject) != 48 {
				continue
			}

			// Skip duplicates in this session
			if processedEsubs[subject] {
				continue
			}

			// Skip cached esubs (replay protection)
			if cache != nil && cache.HasReplay(subject) {
				continue
			}

			articlesToFetch = append(articlesToFetch, articleNum)
			articleSubjects = append(articleSubjects, subject)
			articlesFound++
		}

		if config.Verbose && len(articlesToFetch) > 0 {
			fmt.Printf("Batch %d-%d: found %d valid esub articles\n",
				batchStart, batchEnd, len(articlesToFetch))
		}

		// Fetch individual articles
		for i, num := range articlesToFetch {
			subject := articleSubjects[i]
			processedEsubs[subject] = true

			article, err := fetchArticleWithCache(conn, reader, num, config.Key, subject,
				esubeValidator, downloadedParts, config)
			if err != nil {
				if config.Verbose {
					fmt.Printf("Warning: failed to fetch article %s: %v\n", num, err)
				}
				continue
			}
			if article != nil {
				articles = append(articles, article)
				articlesDownloaded++
				if config.Verbose {
					fmt.Printf("  ✓ %s part %d/%d (article %s)\n",
						article.Filename, article.Part, article.Total, num)
				}
			}
		}

		// Update state for resume (only when not using -latest)
		if config.Latest == 0 {
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
	}

	elapsed := time.Since(startTime).Seconds()
	fmt.Printf("\nDownload complete: %d articles found, %d downloaded in %.1f seconds\n",
		articlesFound, articlesDownloaded, elapsed)

	return articles, nil
}

// calculateHash computes SHA3-256 hash of content
func calculateHash(content []byte) string {
	hash := sha3.Sum256(content)
	return hex.EncodeToString(hash[:])
}

// fetchArticleWithCache retrieves a single article with caching
func fetchArticleWithCache(conn net.Conn, reader *bufio.Reader, articleNum, key, subject string,
	esubeValidator *Esub, downloadedParts map[string]bool, config Config) (*Article, error) {
	// Validate esub BEFORE downloading article body
	if !esubeValidator.Validate(subject) {
		return nil, nil
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
	header.Set("Subject", subject)
	for {
		line, err := reader.ReadString('\n')
		if err != nil {
			return nil, fmt.Errorf("error reading article %s: %v", articleNum, err)
		}
		line = strings.TrimRight(line, "\r\n")
		if line == "" {
			break
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
			break
		}
		if strings.HasPrefix(line, "..") {
			line = line[1:]
		}
		body.WriteString(line)
	}
	// Decode base64 body
	decoded, err := base64.StdEncoding.DecodeString(body.String())
	if err != nil {
		decoded, err = base64.URLEncoding.DecodeString(body.String())
		if err != nil {
			if config.Verbose {
				fmt.Printf("Warning: failed to decode base64 for article %s: %v\n", articleNum, err)
			}
			return nil, nil
		}
	}
	// Parse X-Content header for file information
	var part, total int
	var filename string
	xContent := header.Get("X-Content")
	if xContent != "" && strings.Contains(xContent, "Part [") {
		startIdx := strings.Index(xContent, "[")
		endIdx := strings.Index(xContent, "]")
		if startIdx != -1 && endIdx != -1 && endIdx > startIdx {
			partInfo := xContent[startIdx+1 : endIdx]
			parts := strings.Split(partInfo, "/")
			if len(parts) == 2 {
				part, _ = strconv.Atoi(strings.TrimSpace(parts[0]))
				total, _ = strconv.Atoi(strings.TrimSpace(parts[1]))
			}
			if endIdx+2 < len(xContent) {
				filename = strings.TrimSpace(xContent[endIdx+2:])
			}
		}
	}
	// Skip if incomplete information
	if filename == "" || part == 0 || total == 0 {
		if config.Verbose {
			fmt.Printf("Warning: incomplete X-Content header in article %s: %s\n", articleNum, xContent)
		}
		return nil, nil
	}
	// Calculate content hash
	contentHash := calculateHash(decoded)
	// Create cache key for this file part
	partCacheKey := fmt.Sprintf("%s:%d:%s", filename, total, contentHash[:16])
	// Skip if already downloaded in this session
	if downloadedParts[partCacheKey] {
		if config.Verbose {
			fmt.Printf("Skipping duplicate part %d/%d of %s (already downloaded this session)\n",
				part, total, filename)
		}
		return nil, nil
	}
	downloadedParts[partCacheKey] = true
	// Check file cache to avoid duplicates across sessions
	if cache != nil {
		if cache.HasFile(filename, part, total, contentHash) {
			if config.Verbose {
				fmt.Printf("Skipping cached part %d/%d of %s\n", part, total, filename)
			}
			return nil, nil
		}
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
	blockSize := blockSizeKB * 1024
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

// createArticles creates Article objects from file blocks
func createArticles(filename string, blocks [][]byte, config Config) ([]*Article, error) {
	var articles []*Article
	esube := &Esub{key: config.Key}
	totalParts := len(blocks)
	for i, block := range blocks {
		subject, err := esube.Generate()
		if err != nil {
			return nil, fmt.Errorf("failed to generate esub for part %d: %v", i+1, err)
		}
		header := make(textproto.MIMEHeader)
		if !config.EmailMode {
			fromValue := "Anonymous <anonymous@domain.tld>"
			if config.FromHeader != "" {
				fromValue = config.FromHeader
			}
			header.Set("From", fromValue)
		}
		if config.To != "" {
			header.Set("To", config.To)
		}
		header.Set("Subject", subject)
		header.Set("Newsgroups", config.Newsgroups)
		header.Set("X-Content", fmt.Sprintf("Part [%d/%d] %s", i+1, totalParts, filename))
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

// sendArticles posts multiple articles to NNTP server
func sendArticles(articles []*Article, config Config) error {
	verbosePrintln(config, "Connecting to NNTP server...")
	conn, err := dialNNTP(config.NNTP, config.UseTLS, config.ProxyPort)
	if err != nil {
		return fmt.Errorf("failed to connect to NNTP server: %v", err)
	}
	defer conn.Close()
	if err := conn.SetReadDeadline(time.Now().Add(time.Duration(config.Timeout) * time.Second)); err != nil {
		fmt.Printf("Warning: couldn't set timeout: %v\n", err)
	}
	reader := bufio.NewReader(conn)
	greeting, err := reader.ReadString('\n')
	if err != nil {
		return fmt.Errorf("server greeting failed: %v", err)
	}
	verbosePrintf(config, "Server greeting: %s", greeting)
	verbosePrintf(config, "Posting %d articles...\n", len(articles))
	for i, article := range articles {
		if err := postArticle(conn, article, config.Newsgroups, config); err != nil {
			return fmt.Errorf("failed to post article %d: %v", i+1, err)
		}
		fmt.Printf("Posted article %d/%d for %s (esub: %s)\n", i+1, len(articles), article.Filename, article.Esub)
		time.Sleep(500 * time.Millisecond)
	}
	fmt.Fprintf(conn, "QUIT\r\n")
	verbosePrintln(config, "All articles posted successfully")
	return nil
}

// reconstructFile reconstructs original files from article parts
func reconstructFile(articles []*Article, outputDir string, config Config) error {
	if len(articles) == 0 {
		if config.Verbose {
			fmt.Println("No articles to reconstruct")
		}
		return errors.New("no articles to reconstruct")
	}
	verbosePrintln(config, "Reconstructing files from articles...")
	verbosePrintf(config, "Total articles to process: %d\n", len(articles))
	files := make(map[string]map[int][]*Article)
	for _, article := range articles {
		if article.Filename != "" && article.Part > 0 && article.Total > 0 {
			if files[article.Filename] == nil {
				files[article.Filename] = make(map[int][]*Article)
			}
			files[article.Filename][article.Total] = append(files[article.Filename][article.Total], article)
		}
	}
	verbosePrintf(config, "Found %d unique files\n", len(files))
	reconstructedCount := 0
	for filename, totalMap := range files {
		if config.Verbose {
			fmt.Printf("\nProcessing file: %s\n", filename)
			fmt.Printf("Found %d different versions (different totals)\n", len(totalMap))
		}
		var bestTotal int
		var bestArticles []*Article
		var bestCompleteness float64
		for total, articles := range totalMap {
			if config.Verbose {
				fmt.Printf("  Version with %d total parts: found %d articles\n", total, len(articles))
			}
			uniqueParts := make(map[int]bool)
			for _, article := range articles {
				uniqueParts[article.Part] = true
			}
			completeness := float64(len(uniqueParts)) / float64(total)
			if config.Verbose {
				fmt.Printf("    Completeness: %.1f%% (%d/%d)\n", completeness*100, len(uniqueParts), total)
			}
			if completeness > bestCompleteness ||
				(completeness == bestCompleteness && total > bestTotal) {
				bestTotal = total
				bestArticles = articles
				bestCompleteness = completeness
			}
		}
		if bestCompleteness == 0 {
			if config.Verbose {
				fmt.Printf("No usable articles for %s\n", filename)
			}
			continue
		}
		if err := reconstructSingleFile(filename, bestTotal, bestArticles, outputDir, config); err != nil {
			if config.Verbose {
				fmt.Printf("Error reconstructing %s: %v\n", filename, err)
			}
		} else {
			reconstructedCount++
		}
	}
	verbosePrintf(config, "\nReconstruction complete. Successfully reconstructed %d files.\n", reconstructedCount)
	return nil
}

// reconstructSingleFile reconstructs a single file from its articles
func reconstructSingleFile(filename string, total int, articles []*Article, outputDir string, config Config) error {
	partMap := make(map[int]*Article)
	for _, article := range articles {
		if _, exists := partMap[article.Part]; !exists {
			partMap[article.Part] = article
		} else if config.Verbose {
			fmt.Printf("  Duplicate part %d, keeping first\n", article.Part)
		}
	}
	var sortedArticles []*Article
	for i := 1; i <= total; i++ {
		if article, exists := partMap[i]; exists {
			sortedArticles = append(sortedArticles, article)
		}
	}
	sort.Slice(sortedArticles, func(i, j int) bool {
		return sortedArticles[i].Part < sortedArticles[j].Part
	})
	if len(sortedArticles) != total {
		if config.Verbose {
			fmt.Printf("  Warning: incomplete file (%d/%d parts)\n", len(sortedArticles), total)
			fmt.Printf("  Missing parts: ")
			for i := 1; i <= total; i++ {
				if _, exists := partMap[i]; !exists {
					fmt.Printf("%d ", i)
				}
			}
			fmt.Println()
		}
		filename = fmt.Sprintf("%s_INCOMPLETE_%dof%d", filename, len(sortedArticles), total)
	}
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
	if config.Verbose {
		fmt.Printf("  Successfully reconstructed: %s (%d/%d parts)\n",
			outputPath, len(sortedArticles), total)
	}
	return nil
}

// saveManifest creates a manifest file for easy reconstruction
func saveManifest(files []string, blockSizeKB int, totalArticles int) {
	var manifest []ManifestEntry
	articleCounter := 1
	for _, filename := range files {
		fileInfo, err := os.Stat(filename)
		if err != nil {
			continue
		}
		fileSizeKB := fileInfo.Size() / 1024
		estimatedParts := int(fileSizeKB) / blockSizeKB
		if int(fileSizeKB)%blockSizeKB != 0 {
			estimatedParts++
		}
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

// loadState loads state for a newsgroup from disk
func loadState(group string) error {
	stateFileName := fmt.Sprintf("%s.json", group)
	path := filepath.Join(".", stateFileName)
	data, err := os.ReadFile(path)
	if err != nil {
		if os.IsNotExist(err) {
			return nil
		}
		return fmt.Errorf("failed to read state file: %v", err)
	}
	stateMutex.Lock()
	defer stateMutex.Unlock()
	return json.Unmarshal(data, &state)
}

// saveState saves state for a newsgroup to disk
func saveState(group string) error {
	stateFileName := fmt.Sprintf("%s.json", group)
	path := filepath.Join(".", stateFileName)
	stateMutex.RLock()
	data, err := json.MarshalIndent(state, "", "  ")
	stateMutex.RUnlock()
	if err != nil {
		return fmt.Errorf("failed to serialize state: %v", err)
	}
	tempFile := path + ".tmp"
	if err := os.WriteFile(tempFile, data, 0600); err != nil {
		return fmt.Errorf("failed to write temp state file: %v", err)
	}
	return os.Rename(tempFile, path)
}

// initCache initializes file-based cache
func initCache() error {
	if !*rcFlag {
		return nil
	}
	path := *dbPath
	if path == "" {
		homeDir, err := os.UserHomeDir()
		if err != nil {
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
	cache.Cleanup()
	return nil
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
	fmt.Println("  -b int           Block size in KB (default: 32, max: 256)")
	fmt.Println("  -e               Mixmaster email mode (omits From: header)")
	fmt.Println("  -f string        Custom From: header (default: Anonymous <anonymous@domain.tld>)")
	fmt.Println("  -t string        To: address (for Mixmaster email mode)")
	fmt.Println("")
	fmt.Println("NNTP Options:")
	fmt.Println("  -tls             Use STARTTLS for encrypted connection")
	fmt.Println("  -latest int      Download only last N articles (0 = all, default: 0)")
	fmt.Println("  -batch int       Maximum batch size for XOVER command (default: 500)")
	fmt.Println("  -timeout int     Read timeout in seconds (default: 1200)")
	fmt.Println("")
	fmt.Println("Output Options:")
	fmt.Println("  -v               Verbose output mode (shows progress and details)")
	fmt.Println("")
	fmt.Println("Proxy Options:")
	fmt.Println("  -pp int          SOCKS5 proxy port (0 = no proxy, default: 9050)")
	fmt.Println("")
	fmt.Println("Cache & Resume Options:")
	fmt.Println("  -rc              Enable replay cache and file cache")
	fmt.Println("  -dbpath string   Custom path for cache JSON file")
	fmt.Println("")
	fmt.Println("Behavior Notes:")
	fmt.Println("  • Without -rc:        Downloads all articles from beginning")
	fmt.Println("  • With -rc only:      Downloads all articles + saves state/cache")
	fmt.Println("  • With -rc -latest N: Downloads only last N articles (ignores state)")
	fmt.Println("  • State file:         <newsgroup>.json tracks last downloaded article")
	fmt.Println("")
	fmt.Println("Examples:")
	fmt.Println("  Send file:         b4u -s -k \"my-password\" -n alt.test -S news.server.com:119 file.zip")
	fmt.Println("  Receive all:       b4u -r -k \"my-password\" -n alt.test -S news.server.com:119 -rc")
	fmt.Println("  Last 250 articles: b4u -r -k \"my-password\" -n alt.test -S news.server.com:119 -latest 250")
	fmt.Println("  Resume new only:   b4u -r -k \"my-password\" -n alt.test -S news.server.com:119 -rc")
	fmt.Println("  Verbose output:    b4u -r -k \"my-password\" -n alt.test -S news.server.com:119 -v -rc")
	fmt.Println("  No proxy:          b4u -r -k \"my-password\" -n alt.test -S news.server.com:119 -pp 0 -rc")
	fmt.Println("  Large blocks:      b4u -s -k \"my-password\" -n alt.test -S news.server.com:119 -b 256 file.zip")
	fmt.Println("  Custom From:  b4u -s -k \"my-password\" -n alt.test -S news.server.com:119 -f \"John Doe <john@example.com>\" file.zip")
}

func main() {
	key := flag.String("k", "", "esub key password")
	to := flag.String("t", "", "To: address (for email)")
	fromHeader := flag.String("f", "", "Custom From: header (default: Anonymous <anonymous@domain.tld>)")
	newsgroups := flag.String("n", "", "Newsgroups (comma separated)")
	blockSize := flag.Int("b", 32, "Block size in KB (default 32)")
	sendFlag := flag.Bool("s", false, "Send all files")
	receiveFlag := flag.Bool("r", false, "Receive all files from specified newsgroup")
	nntpServer := flag.String("S", "", "NNTP server:port")
	proxyPort := flag.Int("pp", 9050, "SOCKS5 proxy port (0 = no proxy)")
	emailMode := flag.Bool("e", false, "Email mode (no From: header)")
	useTLS := flag.Bool("tls", false, "Use STARTTLS for encrypted connection")
	latest := flag.Int("latest", 0, "Download only last N articles (0 = all)")
	maxBatch := flag.Int("batch", 500, "Maximum batch size for XOVER command")
	timeout := flag.Int("timeout", 1200, "Read timeout in seconds")
	resumeFlag := flag.Bool("resume", false, "Resume download from last fetched article (requires -rc)")
	verboseFlag := flag.Bool("v", false, "Verbose output mode")
	flag.Usage = printUsage
	flag.Parse()

	if len(os.Args) == 1 {
		printUsage()
		os.Exit(0)
	}

	if *key == "" {
		fmt.Println("Error: esub key (-k) is required")
		printUsage()
		os.Exit(1)
	}

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
		UseTLS:     *useTLS,
		Latest:     *latest,
		MaxBatch:   *maxBatch,
		Timeout:    *timeout,
		Verbose:    *verboseFlag,
	}

	if *rcFlag {
		if config.Verbose {
			fmt.Println("Cache enabled")
		}
		if err := initCache(); err != nil {
			fmt.Printf("Warning: cache initialization failed: %v\n", err)
			fmt.Println("Continuing without cache...")
		} else if config.Verbose {
			fmt.Printf("Cache loaded from: %s\n", cache.filePath)
			fmt.Printf("Replay cache entries: %d\n", len(cache.ReplayCache))
			fmt.Printf("File cache entries: %d\n", len(cache.FileCache))
		}
	}

	defer func() {
		if cache != nil {
			if err := cache.Save(); err != nil {
				fmt.Printf("Warning: failed to save cache: %v\n", err)
			} else if config.Verbose {
				fmt.Println("Cache saved successfully")
			}
		}
	}()

	if config.Verbose {
		fmt.Println("Verbose mode enabled")
		fmt.Printf("Configuration:\n")
		fmt.Printf("  Block size: %d KB\n", config.BlockSize)
		fmt.Printf("  Max batch: %d\n", config.MaxBatch)
		fmt.Printf("  Days: %d\n", config.Days)
		fmt.Printf("  Latest: %d\n", config.Latest)
		fmt.Printf("  Timeout: %d seconds\n", config.Timeout)
		fmt.Printf("  Proxy port: %d\n", config.ProxyPort)
		if config.ProxyPort == 0 {
			fmt.Printf("  Proxy: disabled\n")
		}
		if config.UseTLS {
			fmt.Printf("  STARTTLS: enabled\n")
		}
		if *rcFlag {
			fmt.Printf("  Cache: enabled\n")
		}
	}

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
			blocks, err := splitFile(filename, config.BlockSize)
			if err != nil {
				fmt.Printf("Error splitting file %s: %v\n", filename, err)
				continue
			}
			fmt.Printf("Split %s into %d blocks of %d KB each\n", filename, len(blocks), config.BlockSize)
			articles, err := createArticles(filepath.Base(filename), blocks, config)
			if err != nil {
				fmt.Printf("Error creating articles for %s: %v\n", filename, err)
				continue
			}
			err = sendArticles(articles, config)
			if err != nil {
				fmt.Printf("Error sending articles for %s: %v\n", filename, err)
			} else {
				fmt.Printf("Successfully sent %d articles for %s\n", len(articles), filename)
			}
		}
	} else if config.Receive {
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
		if config.Verbose {
			fmt.Println("Starting receive mode...")
		}
		if config.Latest == 0 {
			if err := loadState(config.Newsgroups); err != nil {
				if config.Verbose {
					fmt.Printf("Warning: failed to load state: %v\n", err)
				}
			}
		}
		conn, err := dialNNTP(config.NNTP, config.UseTLS, config.ProxyPort)
		if err != nil {
			fmt.Printf("Connection failed: %v\n", err)
			os.Exit(1)
		}
		defer conn.Close()
		if err := conn.SetReadDeadline(time.Now().Add(time.Duration(config.Timeout) * time.Second)); err != nil {
			fmt.Printf("Warning: couldn't set timeout: %v\n", err)
		}
		reader := bufio.NewReader(conn)
		greeting, err := reader.ReadString('\n')
		if err != nil {
			fmt.Printf("Server greeting failed: %v\n", err)
			os.Exit(1)
		}
		if config.Verbose {
			fmt.Printf("Server greeting: %s", greeting)
		}
		articles, err := fetchArticles(conn, config, *resumeFlag)
		if err != nil {
			fmt.Printf("Error fetching articles: %v\n", err)
			os.Exit(1)
		}
		if len(articles) > 0 {
			if err := reconstructFile(articles, ".", config); err != nil {
				fmt.Printf("Error reconstructing files: %v\n", err)
			}
		} else {
			fmt.Println("No valid articles found")
		}
		fmt.Fprintf(conn, "QUIT\r\n")
	} else {
		files := flag.Args()
		if len(files) == 0 {
			fmt.Println("Error: no files specified")
			printUsage()
			os.Exit(1)
		}
		totalArticles := 0
		allArticlesInfo := make([]struct {
			filename string
			parts    int
		}, 0)
		for _, filename := range files {
			blocks, err := splitFile(filename, config.BlockSize)
			if err != nil {
				fmt.Printf("Error splitting file %s: %v\n", filename, err)
				continue
			}
			fmt.Printf("Split %s into %d blocks of %d KB each\n", filename, len(blocks), config.BlockSize)
			articles, err := createArticles(filepath.Base(filename), blocks, config)
			if err != nil {
				fmt.Printf("Error creating articles for %s: %v\n", filename, err)
				continue
			}
			allArticlesInfo = append(allArticlesInfo, struct {
				filename string
				parts    int
			}{
				filename: filepath.Base(filename),
				parts:    len(articles),
			})
			for i, article := range articles {
				articleNumber := totalArticles + i + 1
				articleFile := fmt.Sprintf("%04d.txt", articleNumber)
				var buf bytes.Buffer
				writeHeadersInOrder(&buf, article.Header, config)
				buf.WriteString("\r\n")
				encoded := base64.StdEncoding.EncodeToString(article.Body)
				for i := 0; i < len(encoded); i += 76 {
					end := i + 76
					if end > len(encoded) {
						end = len(encoded)
					}
					buf.WriteString(encoded[i:end] + "\r\n")
				}
				buf.WriteString(".\r\n")
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
		if totalArticles > 0 {
			fmt.Printf("\nTotal articles saved: %d\n", totalArticles)
			fmt.Println("Files created: 0001.txt, 0002.txt, ...")
			saveManifest(files, config.BlockSize, totalArticles)
			fmt.Println("\nSummary of created files:")
			for _, info := range allArticlesInfo {
				fmt.Printf("  %s: %d parts\n", info.filename, info.parts)
			}
			fmt.Printf("\nTo send all articles to Usenet:\n")
			fmt.Printf("  b4u -s -k \"%s\" -n \"newsgroup\" -S \"server:port\" *.txt\n", config.Key)
		}
	}
}
