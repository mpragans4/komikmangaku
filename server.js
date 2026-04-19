const express = require("express");
const cheerio = require("cheerio");
const compression = require("compression");
const rateLimit = require("express-rate-limit");
const http = require("http");
const https = require("https");
const { URL } = require("url");
const crypto = require("crypto");
const path = require("path");
const fs = require("fs");

// --- Load custom CSS at startup ---
let CUSTOM_CSS = "";
try {
  CUSTOM_CSS = fs.readFileSync(path.join(__dirname, "public", "css", "custom.css"), "utf-8");
} catch {
  console.warn("[WARN] public/css/custom.css not found, custom UI will not be applied");
}

// ============================================================
// CONFIGURATION
// ============================================================
const CONFIG = {
  // Origin site to mirror
  ORIGIN_HOST: process.env.ORIGIN_HOST || "komik.mangaku.asia",
  ORIGIN_PROTOCOL: process.env.ORIGIN_PROTOCOL || "https",

  // Your mirror domain (set this to your actual domain)
  MIRROR_DOMAIN: process.env.MIRROR_DOMAIN || "",

  // Server port
  PORT: parseInt(process.env.PORT, 10) || 3000,

  // Cache TTL in seconds
  CACHE_TTL: parseInt(process.env.CACHE_TTL, 10) || 300,

  // Max cache entries
  MAX_CACHE_ENTRIES: parseInt(process.env.MAX_CACHE_ENTRIES, 10) || 500,

  // User agent for fetching from origin
  USER_AGENT:
    process.env.USER_AGENT ||
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36",

  // Rate limit per IP (requests per 15 min window)
  RATE_LIMIT: parseInt(process.env.RATE_LIMIT, 10) || 200,

  // Whitelisted external CDN domains to proxy images from
  IMAGE_PROXY_DOMAINS: (process.env.IMAGE_PROXY_DOMAINS || "").split(",").filter(Boolean).concat([
    "anichin.blog",
    "s25.anichin.blog",
    "samehadaku.today",
    "i0.wp.com",
    "i1.wp.com",
    "i2.wp.com",
    "i3.wp.com",
    "bp.blogspot.com",
    "1.bp.blogspot.com",
    "2.bp.blogspot.com",
    "3.bp.blogspot.com",
    "4.bp.blogspot.com",
  ]),
};

// ============================================================
// IN-MEMORY CACHE
// ============================================================
class SimpleCache {
  constructor(maxEntries, defaultTTL) {
    this.store = new Map();
    this.maxEntries = maxEntries;
    this.defaultTTL = defaultTTL * 1000;
  }

  get(key) {
    const entry = this.store.get(key);
    if (!entry) return null;
    if (Date.now() > entry.expires) {
      this.store.delete(key);
      return null;
    }
    return entry.value;
  }

  set(key, value, ttl) {
    // Evict oldest entries if at capacity
    if (this.store.size >= this.maxEntries) {
      const oldest = this.store.keys().next().value;
      this.store.delete(oldest);
    }
    this.store.set(key, {
      value,
      expires: Date.now() + (ttl ? ttl * 1000 : this.defaultTTL),
    });
  }

  clear() {
    this.store.clear();
  }
}

const cache = new SimpleCache(CONFIG.MAX_CACHE_ENTRIES, CONFIG.CACHE_TTL);

// ============================================================
// HELPER: Fetch from origin with redirect following
// ============================================================
function fetchFromOrigin(targetUrl, method, headers, body) {
  return new Promise((resolve, reject) => {
    const parsedUrl = new URL(targetUrl);
    const client = parsedUrl.protocol === "https:" ? https : http;

    const reqHeaders = { ...headers };
    reqHeaders["host"] = parsedUrl.hostname;
    reqHeaders["user-agent"] = CONFIG.USER_AGENT;
    // Remove encoding to get raw text for rewriting
    delete reqHeaders["accept-encoding"];
    // Remove potentially problematic headers
    delete reqHeaders["if-none-match"];
    delete reqHeaders["if-modified-since"];

    const options = {
      hostname: parsedUrl.hostname,
      port: parsedUrl.port || (parsedUrl.protocol === "https:" ? 443 : 80),
      path: parsedUrl.pathname + parsedUrl.search,
      method: method,
      headers: reqHeaders,
      // Don't auto-follow redirects — we handle them ourselves
      followRedirects: false,
    };

    const req = client.request(options, (res) => {
      // Handle redirects manually so we can rewrite Location headers
      if ([301, 302, 303, 307, 308].includes(res.statusCode) && res.headers.location) {
        const redirectUrl = new URL(res.headers.location, targetUrl).toString();
        // If redirecting within origin, follow it
        const redirectParsed = new URL(redirectUrl);
        if (
          redirectParsed.hostname === CONFIG.ORIGIN_HOST ||
          redirectParsed.hostname === parsedUrl.hostname
        ) {
          return fetchFromOrigin(redirectUrl, "GET", headers, null).then(resolve, reject);
        }
        // External redirect — return as-is
        resolve({
          statusCode: res.statusCode,
          headers: res.headers,
          body: Buffer.alloc(0),
          redirectUrl: redirectUrl,
        });
        return;
      }

      const chunks = [];
      res.on("data", (chunk) => chunks.push(chunk));
      res.on("end", () => {
        resolve({
          statusCode: res.statusCode,
          headers: res.headers,
          body: Buffer.concat(chunks),
        });
      });
    });

    req.on("error", reject);
    req.setTimeout(15000, () => {
      req.destroy();
      reject(new Error("Request to origin timed out"));
    });

    if (body && method !== "GET" && method !== "HEAD") {
      req.write(body);
    }
    req.end();
  });
}

// ============================================================
// HTML REWRITING ENGINE
// ============================================================

// Regex to match external CDN image URLs that need proxying
const EXTERNAL_IMG_REGEX = /https?:\/\/(?:s\d+\.anichin\.blog|(?:i\d+\.)?wp\.com|samehadaku\.today|\d+\.bp\.blogspot\.com)[^\s"'<>)]+/g;

// Convert direct anichin.blog URLs to wp.com CDN (bypass Cloudflare)
function convertToWpCdn(url) {
  // s25.anichin.blog/path → i0.wp.com/s25.anichin.blog/path
  const match = url.match(/^https?:\/\/(s\d+\.anichin\.blog\/.+)$/);
  if (match) {
    return `https://i0.wp.com/${match[1]}`;
  }
  // samehadaku.today/path → i0.wp.com/samehadaku.today/path
  const match2 = url.match(/^https?:\/\/(samehadaku\.today\/.+)$/);
  if (match2) {
    return `https://i0.wp.com/${match2[1]}`;
  }
  return url;
}

function proxyImageUrl(url, mirrorBase) {
  // First convert CF-blocked domains to wp.com CDN
  const cdnUrl = convertToWpCdn(url);
  return `${mirrorBase}/img-proxy?url=${encodeURIComponent(cdnUrl)}`;
}

function rewriteExternalImageUrls(text, mirrorBase) {
  return text.replace(EXTERNAL_IMG_REGEX, (match) => {
    return proxyImageUrl(match, mirrorBase);
  });
}

function rewriteHTML(html, mirrorDomain, originHost, requestPath) {
  const $ = cheerio.load(html, { decodeEntities: false });

  const originPatterns = [
    `https://${originHost}`,
    `http://${originHost}`,
    `//${originHost}`,
  ];
  const mirrorBase = `https://${mirrorDomain}`;

  // --- 0. REMOVE ADS & TRACKING ---
  $("#lazy-ads-header-container").remove();
  $("#teaser3").remove();
  $(".ads-header").remove();
  $(".ads-floating-bottom").remove();
  $(".ads").remove();
  $('[id^="lazy-ads"]').remove();
  $('template[id*="ads"]').remove();
  $('script[src*="dtscout"]').remove();
  $('script[src*="cloudflareinsights"]').remove();
  $('script[src*="rocket-loader"]').remove();
  $('script[src*="histats"]').remove();
  $('script[src*="js15_as"]').remove();
  // Remove Histats inline scripts and related elements
  $("script").each((_, el) => {
    const content = $(el).html() || "";
    if (content.includes("Histats") || content.includes("_Hasync") || content.includes("histats")) {
      $(el).remove();
    }
  });
  // Remove Histats tracking pixel and comments
  $('img[src*="histats"]').closest("a").remove();
  $('img[src*="histats"]').remove();
  $('a[href*="histats"]').remove();

  // --- 0b. FIX CLOUDFLARE ROCKET LOADER MANGLING ---
  // Rocket Loader changes type="text/javascript" to type="<hash>-text/javascript"
  // and adds data-cf-modified-<hash> attributes. Restore them.
  $("script").each((_, el) => {
    const scriptType = $(el).attr("type") || "";
    // Fix mangled script type (e.g. "26d2a5deb4a01a73156b6b72-text/javascript")
    if (scriptType.match(/^[a-f0-9]+-text\/javascript$/)) {
      $(el).attr("type", "text/javascript");
    }
    // Remove data-cf-modified-* attributes
    const attribs = el.attribs || {};
    for (const attr of Object.keys(attribs)) {
      if (attr.startsWith("data-cf-modified-")) {
        $(el).removeAttr(attr);
      }
    }
  });
  // Also fix onclick/event handlers that rocket loader wraps with cf check
  $("*").each((_, el) => {
    const attribs = el.attribs || {};
    for (const [attr, val] of Object.entries(attribs)) {
      if (attr.startsWith("data-cf-modified-")) {
        $(el).removeAttr(attr);
      }
      // Fix onclick etc. that have "if (!window.__cfRLUnblockHandlers) return false;"
      if (typeof val === "string" && val.includes("__cfRLUnblockHandlers")) {
        const cleaned = val
          .replace(/if\s*\(\s*!window\.__cfRLUnblockHandlers\s*\)\s*return\s*false;\s*/g, "");
        $(el).attr(attr, cleaned);
      }
    }
  });

  // --- 1. CANONICAL TAG: ensure single, correct canonical ---
  $('link[rel="canonical"]').remove();
  $("head").append(
    `<link rel="canonical" href="${mirrorBase}${requestPath}" />`
  );

  // --- 2. META ROBOTS: ensure indexing is allowed ---
  $('meta[name="robots"]').remove();
  $("head").append('<meta name="robots" content="index, follow" />');

  // --- 2b. INJECT CUSTOM CSS FOR MODERN UI ---
  if (CUSTOM_CSS) {
    $("head").append(`<style id="mirror-custom-css">${CUSTOM_CSS}</style>`);
  }

  // --- 3. OG / TWITTER META TAGS: rewrite URLs ---
  $(
    'meta[property="og:url"], meta[property="og:image"], meta[name="twitter:image"], meta[name="twitter:url"]'
  ).each((_, el) => {
    let content = $(el).attr("content");
    if (content) {
      content = replaceOriginUrls(content, originPatterns, mirrorBase);
      content = rewriteExternalImageUrls(content, mirrorBase);
      $(el).attr("content", content);
    }
  });

  // --- 4. REWRITE ALL HREF / SRC / ACTION / SRCSET ATTRIBUTES ---
  $("[href]").each((_, el) => {
    const val = $(el).attr("href");
    if (val) $(el).attr("href", replaceOriginUrls(val, originPatterns, mirrorBase));
  });

  $("[src]").each((_, el) => {
    let val = $(el).attr("src");
    if (val) {
      val = replaceOriginUrls(val, originPatterns, mirrorBase);
      val = rewriteExternalImageUrls(val, mirrorBase);
      $(el).attr("src", val);
    }
  });

  $("[action]").each((_, el) => {
    const val = $(el).attr("action");
    if (val) $(el).attr("action", replaceOriginUrls(val, originPatterns, mirrorBase));
  });

  $("[srcset]").each((_, el) => {
    let val = $(el).attr("srcset");
    if (val) {
      val = replaceOriginUrls(val, originPatterns, mirrorBase);
      val = rewriteExternalImageUrls(val, mirrorBase);
      $(el).attr("srcset", val);
    }
  });

  $("[data-src]").each((_, el) => {
    let val = $(el).attr("data-src");
    if (val) {
      val = replaceOriginUrls(val, originPatterns, mirrorBase);
      val = rewriteExternalImageUrls(val, mirrorBase);
      $(el).attr("data-src", val);
    }
  });

  $("[data-lazy-src]").each((_, el) => {
    let val = $(el).attr("data-lazy-src");
    if (val) {
      val = replaceOriginUrls(val, originPatterns, mirrorBase);
      val = rewriteExternalImageUrls(val, mirrorBase);
      $(el).attr("data-lazy-src", val);
    }
  });

  // --- 4b. REWRITE ALL data-* ATTRIBUTES containing origin or external CDN URLs ---
  $("*").each((_, el) => {
    const attribs = el.attribs || {};
    for (const [attr, val] of Object.entries(attribs)) {
      if (attr.startsWith("data-") && typeof val === "string") {
        let newVal = val;
        if (val.includes(originHost)) {
          newVal = replaceOriginUrls(newVal, originPatterns, mirrorBase);
        }
        if (EXTERNAL_IMG_REGEX.test(newVal)) {
          EXTERNAL_IMG_REGEX.lastIndex = 0;
          newVal = rewriteExternalImageUrls(newVal, mirrorBase);
        }
        if (newVal !== val) $(el).attr(attr, newVal);
      }
    }
  });

  // --- 5. FIX STRUCTURED DATA (JSON-LD) ---
  $('script[type="application/ld+json"]').each((_, el) => {
    let jsonText = $(el).html();
    if (jsonText) {
      try {
        let jsonData = JSON.parse(jsonText);
        jsonData = fixStructuredData(jsonData, originPatterns, mirrorBase, mirrorDomain);
        $(el).html(JSON.stringify(jsonData, null, 0));
      } catch (e) {
        // If JSON parse fails, just do string replacement
        jsonText = replaceAllOriginUrls(jsonText, originPatterns, mirrorBase);
        $(el).html(jsonText);
      }
    }
  });

  // --- 6. INLINE STYLES: rewrite url() references ---
  $("style").each((_, el) => {
    let css = $(el).html();
    if (css) {
      css = replaceAllOriginUrls(css, originPatterns, mirrorBase);
      css = rewriteExternalImageUrls(css, mirrorBase);
      $(el).html(css);
    }
  });

  $("[style]").each((_, el) => {
    let style = $(el).attr("style");
    if (style) {
      style = replaceAllOriginUrls(style, originPatterns, mirrorBase);
      style = rewriteExternalImageUrls(style, mirrorBase);
      $(el).attr("style", style);
    }
  });

  // --- 7. INLINE SCRIPTS: rewrite origin references ---
  $("script:not([type]), script[type='text/javascript']").each((_, el) => {
    let js = $(el).html();
    if (js && js.includes(originHost)) {
      js = replaceAllOriginUrls(js, originPatterns, mirrorBase);
      // Also handle bare hostname in strings
      js = js.split(originHost).join(mirrorDomain);
      $(el).html(js);
    }
  });

  // --- 8. REMOVE ALTERNATE/HREFLANG POINTING TO ORIGIN ---
  $('link[rel="alternate"]').each((_, el) => {
    const href = $(el).attr("href");
    if (href) {
      $(el).attr("href", replaceOriginUrls(href, originPatterns, mirrorBase));
    }
  });

  // --- 9. BASE TAG ---
  $("base").each((_, el) => {
    const href = $(el).attr("href");
    if (href) {
      $(el).attr("href", replaceOriginUrls(href, originPatterns, mirrorBase));
    }
  });

  // --- 10. STRIP TRACKING HTML COMMENTS ---
  let finalHtml = $.html();
  finalHtml = finalHtml.replace(/<!--\s*Histats\.com[\s\S]*?-->/gi, "");
  finalHtml = finalHtml.replace(/<noscript>[\s\S]*?histats[\s\S]*?<\/noscript>/gi, "");
  return finalHtml;
}

// Replace origin URLs in a single attribute value
function replaceOriginUrls(value, originPatterns, mirrorBase) {
  let result = value;
  for (const pattern of originPatterns) {
    result = result.split(pattern).join(mirrorBase);
  }
  return result;
}

// Replace all origin URLs in a block of text
function replaceAllOriginUrls(text, originPatterns, mirrorBase) {
  let result = text;
  for (const pattern of originPatterns) {
    result = result.split(pattern).join(mirrorBase);
  }
  return result;
}

// Deep fix structured data objects
function fixStructuredData(data, originPatterns, mirrorBase, mirrorDomain) {
  if (typeof data === "string") {
    return replaceAllOriginUrls(data, originPatterns, mirrorBase);
  }
  if (Array.isArray(data)) {
    return data.map((item) =>
      fixStructuredData(item, originPatterns, mirrorBase, mirrorDomain)
    );
  }
  if (typeof data === "object" && data !== null) {
    const fixed = {};
    for (const [key, val] of Object.entries(data)) {
      fixed[key] = fixStructuredData(val, originPatterns, mirrorBase, mirrorDomain);
    }

    // Ensure BreadcrumbList items have proper @id and item URLs
    if (fixed["@type"] === "BreadcrumbList" && Array.isArray(fixed.itemListElement)) {
      fixed.itemListElement = fixed.itemListElement.map((item, index) => {
        if (item["@type"] === "ListItem") {
          // Ensure position is a number
          if (typeof item.position === "string") {
            item.position = parseInt(item.position, 10) || index + 1;
          }
          // Ensure item URL is valid
          if (item.item && typeof item.item === "string") {
            if (!item.item.startsWith("http")) {
              item.item = mirrorBase + item.item;
            }
          }
          if (item.item && typeof item.item === "object" && item.item["@id"]) {
            if (!item.item["@id"].startsWith("http")) {
              item.item["@id"] = mirrorBase + item.item["@id"];
            }
          }
        }
        return item;
      });
    }

    // Ensure WebSite / WebPage schemas reference mirror
    if (fixed["@type"] === "WebSite" || fixed["@type"] === "WebPage") {
      if (fixed.url) {
        fixed.url = replaceAllOriginUrls(fixed.url, originPatterns, mirrorBase);
      }
      if (fixed["@id"]) {
        fixed["@id"] = replaceAllOriginUrls(fixed["@id"], originPatterns, mirrorBase);
      }
    }

    return fixed;
  }
  return data;
}

// Rewrite CSS text
function rewriteCSS(css, mirrorDomain, originHost) {
  const originPatterns = [
    `https://${originHost}`,
    `http://${originHost}`,
    `//${originHost}`,
  ];
  const mirrorBase = `https://${mirrorDomain}`;
  return replaceAllOriginUrls(css, originPatterns, mirrorBase);
}

// ============================================================
// EXPRESS SERVER
// ============================================================
const app = express();

// Trust proxy (for Railway, Render, etc.)
app.set("trust proxy", 1);

// Gzip compression
app.use(compression());

// Rate limiting
const limiter = rateLimit({
  windowMs: 15 * 60 * 1000,
  max: CONFIG.RATE_LIMIT,
  standardHeaders: true,
  legacyHeaders: false,
  message: "Too many requests, please try again later.",
});
app.use(limiter);

// Health check endpoint
app.get("/health", (req, res) => {
  res.status(200).json({ status: "ok", uptime: process.uptime() });
});

// Helper: detect mirror domain from request
function getMirrorDomain(req) {
  return CONFIG.MIRROR_DOMAIN || req.headers["x-forwarded-host"] || req.headers.host;
}

// Robots.txt — serve our own to control crawling
app.get("/robots.txt", (req, res) => {
  const mirrorDomain = getMirrorDomain(req);
  res.type("text/plain").send(
    `User-agent: *
Allow: /

Sitemap: https://${mirrorDomain}/donghua-sitemap.xml
Sitemap: https://${mirrorDomain}/anime-sitemap.xml
`
  );
});

// ============================================================
// IMAGE PROXY — bypass Cloudflare for external CDN images
// ============================================================
function isAllowedProxyDomain(hostname) {
  return CONFIG.IMAGE_PROXY_DOMAINS.some(
    (d) => hostname === d || hostname.endsWith("." + d)
  );
}

function fetchImageFromCDN(imageUrl) {
  return new Promise((resolve, reject) => {
    const parsedUrl = new URL(imageUrl);
    const client = parsedUrl.protocol === "https:" ? https : http;

    const options = {
      hostname: parsedUrl.hostname,
      port: parsedUrl.port || (parsedUrl.protocol === "https:" ? 443 : 80),
      path: parsedUrl.pathname + parsedUrl.search,
      method: "GET",
      headers: {
        "host": parsedUrl.hostname,
        "user-agent": CONFIG.USER_AGENT,
        "accept": "image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8",
        "accept-language": "en-US,en;q=0.9,id;q=0.8",
        "referer": `${CONFIG.ORIGIN_PROTOCOL}://${CONFIG.ORIGIN_HOST}/`,
        "origin": `${CONFIG.ORIGIN_PROTOCOL}://${CONFIG.ORIGIN_HOST}`,
        "sec-fetch-dest": "image",
        "sec-fetch-mode": "no-cors",
        "sec-fetch-site": "cross-site",
        "sec-ch-ua": '"Chromium";v="131", "Not_A Brand";v="24"',
        "sec-ch-ua-mobile": "?0",
        "sec-ch-ua-platform": '"Windows"',
      },
    };

    const req = client.request(options, (res) => {
      // Follow redirects
      if ([301, 302, 303, 307, 308].includes(res.statusCode) && res.headers.location) {
        const redirectUrl = new URL(res.headers.location, imageUrl).toString();
        return fetchImageFromCDN(redirectUrl).then(resolve, reject);
      }

      const chunks = [];
      res.on("data", (chunk) => chunks.push(chunk));
      res.on("end", () => {
        resolve({
          statusCode: res.statusCode,
          headers: res.headers,
          body: Buffer.concat(chunks),
        });
      });
    });

    req.on("error", reject);
    req.setTimeout(20000, () => {
      req.destroy();
      reject(new Error("Image fetch timed out"));
    });
    req.end();
  });
}

app.get("/img-proxy", async (req, res) => {
  try {
    let imageUrl = req.query.url;
    if (!imageUrl) {
      return res.status(400).send("Missing url parameter");
    }

    // Convert CF-blocked domains to wp.com CDN automatically
    imageUrl = convertToWpCdn(imageUrl);

    // Validate URL
    let parsedUrl;
    try {
      parsedUrl = new URL(imageUrl);
    } catch {
      return res.status(400).send("Invalid URL");
    }

    // Security: only allow whitelisted domains
    if (!isAllowedProxyDomain(parsedUrl.hostname)) {
      return res.status(403).send("Domain not allowed");
    }

    // Check cache
    const cacheKey = `imgproxy:${imageUrl}`;
    const cached = cache.get(cacheKey);
    if (cached) {
      for (const [k, v] of Object.entries(cached.headers)) {
        res.setHeader(k, v);
      }
      res.status(cached.statusCode).send(cached.body);
      return;
    }

    const imgRes = await fetchImageFromCDN(imageUrl);

    // If blocked by CF (403), try wp.com CDN fallback
    if (imgRes.statusCode === 403) {
      const wpCdnUrl = convertToWpCdn(imageUrl);
      if (wpCdnUrl !== imageUrl) {
        const retryRes = await fetchImageFromCDN(wpCdnUrl);
        if (retryRes.statusCode === 200) {
          const retryHeaders = {};
          const passH = ["content-type", "last-modified", "etag"];
          for (const h of passH) {
            if (retryRes.headers[h]) retryHeaders[h] = retryRes.headers[h];
          }
          retryHeaders["cache-control"] = "public, max-age=86400, immutable";
          retryHeaders["access-control-allow-origin"] = "*";
          cache.set(cacheKey, { statusCode: 200, headers: retryHeaders, body: retryRes.body }, 3600);
          for (const [k, v] of Object.entries(retryHeaders)) res.setHeader(k, v);
          return res.status(200).send(retryRes.body);
        }
      }
    }

    // Build response headers
    const responseHeaders = {};
    const passHeaders = ["content-type", "last-modified", "etag"];
    for (const h of passHeaders) {
      if (imgRes.headers[h]) responseHeaders[h] = imgRes.headers[h];
    }
    responseHeaders["cache-control"] = "public, max-age=86400, immutable";
    responseHeaders["access-control-allow-origin"] = "*";

    // Cache successful image responses
    if (imgRes.statusCode === 200) {
      cache.set(cacheKey, {
        statusCode: imgRes.statusCode,
        headers: responseHeaders,
        body: imgRes.body,
      }, 3600);
    }

    for (const [k, v] of Object.entries(responseHeaders)) {
      res.setHeader(k, v);
    }
    res.status(imgRes.statusCode).send(imgRes.body);
  } catch (error) {
    console.error("[IMG-PROXY ERROR]", error.message);
    res.status(502).send("Failed to fetch image");
  }
});

// ============================================================
// MAIN PROXY HANDLER
// ============================================================
app.all("*", async (req, res) => {
  try {
    const mirrorDomain = getMirrorDomain(req);
    const requestPath = req.originalUrl;

    // Build origin URL
    const originUrl = `${CONFIG.ORIGIN_PROTOCOL}://${CONFIG.ORIGIN_HOST}${requestPath}`;

    // Check cache for GET requests (include domain in key since HTML is domain-specific)
    const cacheKey = `${mirrorDomain}:${req.method}:${requestPath}`;
    if (req.method === "GET") {
      const cached = cache.get(cacheKey);
      if (cached) {
        for (const [k, v] of Object.entries(cached.headers)) {
          res.setHeader(k, v);
        }
        res.status(cached.statusCode).send(cached.body);
        return;
      }
    }

    // Build headers to forward
    const forwardHeaders = {};
    const skipHeaders = new Set([
      "host",
      "connection",
      "accept-encoding",
      "cf-connecting-ip",
      "cf-ray",
      "cf-visitor",
      "cf-ipcountry",
      "x-forwarded-for",
      "x-forwarded-proto",
      "x-forwarded-host",
    ]);

    for (const [key, val] of Object.entries(req.headers)) {
      if (!skipHeaders.has(key.toLowerCase())) {
        forwardHeaders[key] = val;
      }
    }

    // Collect request body for non-GET
    let body = null;
    if (req.method !== "GET" && req.method !== "HEAD") {
      body = await new Promise((resolve, reject) => {
        const chunks = [];
        req.on("data", (c) => chunks.push(c));
        req.on("end", () => resolve(Buffer.concat(chunks)));
        req.on("error", reject);
      });
    }

    // Fetch from origin
    const originRes = await fetchFromOrigin(originUrl, req.method, forwardHeaders, body);

    // If external redirect, pass it through with rewritten URL
    if (originRes.redirectUrl) {
      const rewrittenLocation = originRes.redirectUrl
        .replace(`https://${CONFIG.ORIGIN_HOST}`, `https://${mirrorDomain}`)
        .replace(`http://${CONFIG.ORIGIN_HOST}`, `https://${mirrorDomain}`)
        .replace(`//${CONFIG.ORIGIN_HOST}`, `//${mirrorDomain}`);
      res.redirect(originRes.statusCode, rewrittenLocation);
      return;
    }

    // Determine content type
    const contentType = (originRes.headers["content-type"] || "").toLowerCase();
    const isXML = contentType.includes("text/xml") || contentType.includes("application/xml")
      || contentType.includes("application/rss+xml") || contentType.includes("application/atom+xml")
      || requestPath.match(/sitemap[^/]*\.xml$/i) || requestPath.match(/\.xml$/i);
    const isHTML = contentType.includes("text/html") && !isXML;
    const isCSS = contentType.includes("text/css");
    const isJS =
      contentType.includes("javascript") || contentType.includes("application/json");

    // Build response headers
    const responseHeaders = {};
    const removeHeaders = new Set([
      "content-encoding",
      "content-length",
      "transfer-encoding",
      "connection",
      "set-cookie",
      "alt-svc",
      "cf-ray",
      "cf-cache-status",
      "server",
      "x-powered-by",
      "strict-transport-security",
      "content-security-policy",
      "x-frame-options",
    ]);

    for (const [key, val] of Object.entries(originRes.headers)) {
      if (!removeHeaders.has(key.toLowerCase())) {
        responseHeaders[key] = val;
      }
    }

    // Add SEO and cache headers
    responseHeaders["x-robots-tag"] = "index, follow";

    let responseBody;

    if (isXML) {
      // XML sitemap rewriting — string-level replacement, do NOT use Cheerio
      let xml = originRes.body.toString("utf-8");
      xml = xml.split(`https://${CONFIG.ORIGIN_HOST}`).join(`https://${mirrorDomain}`);
      xml = xml.split(`http://${CONFIG.ORIGIN_HOST}`).join(`https://${mirrorDomain}`);
      xml = xml.split(`//${CONFIG.ORIGIN_HOST}`).join(`//${mirrorDomain}`);
      xml = xml.split(CONFIG.ORIGIN_HOST).join(mirrorDomain);
      responseBody = xml;
      responseHeaders["content-type"] = "application/xml; charset=utf-8";

      // Cache sitemaps for a moderate period
      if (req.method === "GET" && originRes.statusCode === 200) {
        cache.set(
          cacheKey,
          {
            statusCode: originRes.statusCode,
            headers: responseHeaders,
            body: responseBody,
          },
          300
        );
      }
    } else if (isHTML) {
      // Full HTML rewriting
      let html = originRes.body.toString("utf-8");
      html = rewriteHTML(html, mirrorDomain, CONFIG.ORIGIN_HOST, requestPath);
      responseBody = html;
      responseHeaders["content-type"] = "text/html; charset=utf-8";

      // Generate ETag for de-duplication
      const etag = `"${crypto
        .createHash("md5")
        .update(responseBody)
        .digest("hex")}"`;
      responseHeaders["etag"] = etag;

      // Cache HTML for shorter period
      if (req.method === "GET" && originRes.statusCode === 200) {
        cache.set(
          cacheKey,
          {
            statusCode: originRes.statusCode,
            headers: responseHeaders,
            body: responseBody,
          },
          180
        );
      }
    } else if (isCSS) {
      let css = originRes.body.toString("utf-8");
      css = rewriteCSS(css, mirrorDomain, CONFIG.ORIGIN_HOST);
      responseBody = css;
    } else if (isJS) {
      let text = originRes.body.toString("utf-8");
      text = text.split(CONFIG.ORIGIN_HOST).join(mirrorDomain);
      text = text
        .split(`https://${CONFIG.ORIGIN_HOST}`)
        .join(`https://${mirrorDomain}`);
      responseBody = text;
    } else {
      // Binary content (images, fonts, etc.) — pass through
      responseBody = originRes.body;

      // Cache static assets longer
      if (
        req.method === "GET" &&
        originRes.statusCode === 200 &&
        (contentType.includes("image") ||
          contentType.includes("font") ||
          contentType.includes("woff"))
      ) {
        responseHeaders["cache-control"] = "public, max-age=86400";
        cache.set(
          cacheKey,
          {
            statusCode: originRes.statusCode,
            headers: responseHeaders,
            body: responseBody,
          },
          600
        );
      }
    }

    // Set headers and send response
    for (const [k, v] of Object.entries(responseHeaders)) {
      res.setHeader(k, v);
    }

    res.status(originRes.statusCode).send(responseBody);
  } catch (error) {
    console.error(`[ERROR] ${req.method} ${req.originalUrl}:`, error.message);
    res.status(502).send(`
      <!DOCTYPE html>
      <html><head><title>502 Bad Gateway</title></head>
      <body><h1>502 Bad Gateway</h1><p>The origin server is unreachable.</p></body>
      </html>
    `);
  }
});

// ============================================================
// START SERVER
// ============================================================
app.listen(CONFIG.PORT, "0.0.0.0", () => {
  console.log(`Mirror proxy running on port ${CONFIG.PORT}`);
  console.log(`Origin: ${CONFIG.ORIGIN_PROTOCOL}://${CONFIG.ORIGIN_HOST}`);
  console.log(
    `Mirror domain: ${CONFIG.MIRROR_DOMAIN || "(auto-detect from Host header)"}`
  );
});
