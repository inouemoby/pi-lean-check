import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import { execSync, spawnSync } from "node:child_process";
import { createWriteStream, existsSync, mkdirSync, writeFileSync, rmSync } from "node:fs";
import { get } from "node:https";
import { join } from "node:path";
import { tmpdir, platform, arch, homedir } from "node:os";
import { randomUUID } from "node:crypto";

// ─── Types ───────────────────────────────────────────────────────
interface LeanError {
  line: number;
  col: number;
  msg: string;
}

interface LeanResult {
  valid: boolean;
  errors: LeanError[];
  messages: string[];
}

// ─── Constants ──────────────────────────────────────────────────
const CACHE_DIR = join(homedir(), ".pi", "agent", "extensions", "pi-lean-check", "bin");
const GITHUB_API = "https://api.github.com/repos/leanprover/lean4/releases";

// ─── Platform detection ─────────────────────────────────────────
interface PlatformInfo {
  assetSuffix: string;
  binary: string;
}

function getPlatformInfo(): PlatformInfo | null {
  const p = platform();
  const a = arch();

  if (p === "win32") return { assetSuffix: "windows.zip", binary: "lean.exe" };
  if (p === "darwin" && a === "arm64") return { assetSuffix: "darwin_aarch64.zip", binary: "lean" };
  if (p === "darwin") return { assetSuffix: "darwin.zip", binary: "lean" };
  if (p === "linux" && a === "arm64") return { assetSuffix: "linux_aarch64.zip", binary: "lean" };
  if (p === "linux") return { assetSuffix: "linux.zip", binary: "lean" };
  return null;
}

function leanBinaryPath(): string {
  const info = getPlatformInfo();
  return info ? join(CACHE_DIR, "bin", info.binary) : join(CACHE_DIR, "unknown");
}

function findLeanInCache(info: PlatformInfo): string | null {
  // The zip extracts to: CACHE_DIR/lean-{version}-{platform}/bin/lean.exe
  if (!existsSync(CACHE_DIR)) return null;
  try {
    const searchCmd = platform() === "win32"
      ? 'dir /s /b "' + CACHE_DIR + '\\' + info.binary + '" 2>nul'
      : 'find "' + CACHE_DIR + '" -name "' + info.binary + '" -type f 2>/dev/null';
    const result = execSync(searchCmd, { encoding: "utf8", timeout: 10_000 }).trim();
    const lines = result.split("\n").filter(l => l.includes(info.binary) && !l.includes("lake.exe"));
    if (lines.length > 0 && existsSync(lines[0].trim())) return lines[0].trim();
  } catch { /* search failed */ }
  return null;
}

// ─── Download ───────────────────────────────────────────────────
function downloadFile(url: string, dest: string): Promise<void> {
  mkdirSync(join(dest, ".."), { recursive: true });
  const file = createWriteStream(dest);

  return new Promise((resolve, reject) => {
    function attempt(urlToFetch: string) {
      get(urlToFetch, { headers: { "User-Agent": "pi-lean-check/1.0" } }, (res) => {
        if (res.statusCode === 302 || res.statusCode === 301) {
          file.close();
          rmSync(dest, { force: true });
          attempt(res.headers.location!);
          return;
        }
        if (res.statusCode !== 200) {
          file.close();
          rmSync(dest, { force: true });
          reject(new Error("HTTP " + res.statusCode));
          return;
        }
        res.pipe(file);
        file.on("finish", () => file.close(() => resolve()));
        file.on("error", reject);
      }).on("error", reject);
    }
    attempt(url);
  });
}

async function getReleaseInfo(): Promise<{ tag: string; downloadUrl: string }> {
  const resp = await fetch(GITHUB_API + "/latest", {
    headers: { "User-Agent": "pi-lean-check/1.0" },
  });
  if (!resp.ok) throw new Error("GitHub API error: " + resp.status);
  const data = (await resp.json()) as any;
  const tag = data.tag_name;
  const version = tag.replace(/^v/, "");
  const suffix = getPlatformInfo()?.assetSuffix;
  if (!suffix) throw new Error("Unsupported platform");

  // Match asset name: lean-{version}-{windows/darwin/linux...}.zip
  const assetName = "lean-" + version + "-" + suffix;
  for (const a of data.assets || []) {
    if (a.name === assetName) return { tag, downloadUrl: a.browser_download_url };
  }

  // Fallback: construct URL directly  
  return {
    tag,
    downloadUrl: "https://github.com/leanprover/lean4/releases/download/" + tag + "/" + assetName,
  };
}

// ─── Extract ────────────────────────────────────────────────────
function extractArchive(archivePath: string, destDir: string) {
  mkdirSync(destDir, { recursive: true });
  if (platform() === "win32") {
    execSync(
      'powershell -Command "Expand-Archive -Path \'' + archivePath + '\' -DestinationPath \'' + destDir + '\' -Force"',
      { stdio: "ignore", timeout: 120_000 },
    );
  } else {
    execSync('unzip -o "' + archivePath + '" -d "' + destDir + '"', { stdio: "ignore", timeout: 120_000 });
  }
}

// ─── Ensure Lean is available ───────────────────────────────────
async function ensureLean(
  onProgress: (msg: string) => void,
): Promise<string> {
  const info = getPlatformInfo();
  if (!info) throw new Error("Unsupported platform: " + platform() + "-" + arch());

  // Check if already cached in the expected path
  const bp = leanBinaryPath();
  if (existsSync(bp)) return bp;

  // Search for existing lean binary in cache (from previous extraction)
  const cached = findLeanInCache(info);
  if (cached) {
    // Copy to expected location for consistency
    mkdirSync(join(bp, ".."), { recursive: true });
    try {
      if (platform() === "win32") {
        execSync('copy "' + cached + '" "' + bp + '"', { stdio: "ignore" });
      } else {
        execSync('ln -sf "' + cached + '" "' + bp + '"', { stdio: "ignore" });
      }
    } catch { /* if copy fails, just use cached path */ }
    if (existsSync(bp)) return bp;
    // Fallback: use the cached path directly
    return cached;
  }

  // Need to download
  mkdirSync(CACHE_DIR, { recursive: true });

  const release = await getReleaseInfo();
  onProgress("Downloading Lean 4 " + release.tag + " (~750MB, one-time)...");

  const archiveName = "lean-" + release.tag.replace(/^v/, "") + "-" + info.assetSuffix;
  const archivePath = join(CACHE_DIR, archiveName);
  await downloadFile(release.downloadUrl, archivePath);

  onProgress("Extracting Lean 4...");
  extractArchive(archivePath, CACHE_DIR);
  rmSync(archivePath, { force: true });

  // After extraction, find and cache the binary
  const found = findLeanInCache(info);
  if (found) {
    mkdirSync(join(bp, ".."), { recursive: true });
    try {
      if (platform() === "win32") {
        execSync('copy "' + found + '" "' + bp + '"', { stdio: "ignore" });
      } else {
        execSync('ln -sf "' + found + '" "' + bp + '"', { stdio: "ignore" });
      }
    } catch { /* copy can fail */ }
    if (existsSync(bp)) {
      onProgress("Lean 4 ready ✓");
      return bp;
    }
    return found;
  }

  throw new Error(
    "Lean binary not found after extraction.\n" +
    "Expected under: " + CACHE_DIR + "\n" +
    "Please install Lean 4 manually: https://leanprover-community.github.io/get_started.html",
  );
}

// ─── Run Lean on code ───────────────────────────────────────────
function runLean(code: string, leanBin: string): LeanResult {
  const tmpDir = join(tmpdir(), "lean-" + randomUUID());
  mkdirSync(tmpDir, { recursive: true });

  try {
    const leanFile = join(tmpDir, "check.lean");
    writeFileSync(leanFile, code, "utf8");

    const result = spawnSync(leanBin, [leanFile], {
      cwd: tmpDir,
      encoding: "utf8",
      timeout: 30_000,
      maxBuffer: 1024 * 1024,
    });

    const output = (result.stdout || "") + "\n" + (result.stderr || "");
    const errors: LeanError[] = [];
    const messages: string[] = [];

    for (const line of output.split("\n")) {
      const errMatch = line.match(/(.+\.lean):(\d+):(\d+):\s*(?:error|warning):\s*(.+)/);
      if (errMatch) {
        errors.push({
          line: parseInt(errMatch[2], 10),
          col: parseInt(errMatch[3], 10),
          msg: errMatch[4].trim(),
        });
      } else if (line.trim()) {
        messages.push(line.trim());
      }
    }

    return { valid: errors.length === 0 && result.status === 0, errors, messages };
  } finally {
    try { rmSync(tmpDir, { recursive: true, force: true }); } catch { /* ok */ }
  }
}

// ─── Lean prelude ───────────────────────────────────────────────
const LEAN_PRELUDE = "import Init\n\n";

// ─── Main Extension ─────────────────────────────────────────────
export default function (pi: ExtensionAPI) {
  let leanBin = "";

  // Eagerly download on session start (async, non-blocking)
  pi.on("session_start", async () => {
    try {
      leanBin = await ensureLean(() => {});
    } catch { /* will retry on first tool call */ }
  });

  pi.registerTool({
    name: "lean_check",
    label: "Lean Proof Check",
    description:
      "Verify logical reasoning and mathematical proofs using the Lean 4 theorem prover. Write a formal statement and proof in Lean syntax; this tool compiles and checks it. Use for: verifying logical implications, validating deductive arguments, checking mathematical conjectures, confirming algorithmic invariants, and ensuring reasoning is rigorous.",
    promptSnippet: "Verify logic/proofs with Lean 4 theorem prover (formal verification)",
    promptGuidelines: [
      "Use lean_check to verify any non-trivial logical deduction or mathematical claim. It provides formal, machine-checked verification.",
      "Express reasoning as Lean theorems: `example : <proposition> := by <tactic proof>`.",
      "Lean's Init library provides: propositional logic (∧∨→¬↔), predicates (∀∃), equality (=), natural numbers (Nat), integers (Int), lists, and options.",
      "For multi-step reasoning, prove a lemma first, then use it in the main theorem.",
      "If verification fails, the error messages pinpoint the exact line and column where logic breaks down — use this to fix your reasoning.",
      "When reasoning about programs, state invariants as Lean theorems and verify them.",
      "Lean is based on dependent type theory — your proofs are checked for 100% logical correctness, not just pattern matching.",
    ],
    parameters: Type.Object({
      code: Type.String({
        description:
          "Lean 4 code with theorem(s) to check. Init is pre-imported. Use 'example : <proposition> := by <proof>' format. Each 'example' is one claim to verify. You can write multiple examples separated by newlines.",
      }),
    }),
    async execute(_id, params, signal, onUpdate, _ctx) {
      // Lazy download if not done yet
      if (!leanBin) {
        try {
          leanBin = await ensureLean((msg) => {
            if (!signal?.aborted) {
              onUpdate?.({ content: [{ type: "text", text: msg }] });
            }
          });
        } catch (err: any) {
          return {
            content: [
              {
                type: "text",
                text:
                  "Lean 4 is not available.\n\n" +
                  "Error: " + (err.message || err) + "\n\n" +
                  "Install Lean 4 manually: https://leanprover-community.github.io/get_started.html",
              },
            ],
            isError: true,
          };
        }
      }

      if (signal?.aborted) return { content: [{ type: "text", text: "Cancelled." }] };
      onUpdate?.({ content: [{ type: "text", text: "Running Lean 4 proof checker..." }] });

      const fullCode = LEAN_PRELUDE + params.code;
      const result = runLean(fullCode, leanBin);

      if (result.valid) {
        const clean = result.messages.filter(m => !m.includes("check.lean"));
        return {
          content: [{
            type: "text",
            text: "✓ All proofs verified — logically valid." + (clean.length > 0 ? "\n" + clean.join("\n") : ""),
          }],
          details: { valid: true, errors: [] },
        };
      } else {
        const errLines = result.errors.map(e => "  " + e.line + ":" + e.col + " → " + e.msg).join("\n");
        return {
          content: [{
            type: "text",
            text: "✗ " + result.errors.length + " verification error(s):\n\n" + errLines,
          }],
          details: { valid: false, errors: result.errors },
        };
      }
    },
  });

  // ── /lean-status command ────────────────────────────────────
  pi.registerCommand("lean-status", {
    description: "Check Lean 4 installation status",
    handler: async (_args, ctx) => {
      if (leanBin && existsSync(leanBin)) {
        try {
          const ver = execSync('"' + leanBin + '" --version', { encoding: "utf8", timeout: 5_000 }).trim();
          ctx.ui.notify("✓ Lean 4 available: " + ver, "success");
        } catch {
          ctx.ui.notify("Lean binary found but failed: " + leanBin, "error");
        }
      } else {
        ctx.ui.notify(
          "Lean 4 not cached yet. Will download on first lean_check call (~750MB, one-time).",
          "info",
        );
      }
    },
  });
}
