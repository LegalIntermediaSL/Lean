#!/usr/bin/env python3
"""
Validador automatizado de documentación interactiva y bloques ejecutables Lean 4.

Comprueba dos invariantes de calidad en todo el repositorio (`README.md`, `_sidebar.md` y `docs/**/*.md`):
1. Cero enlaces internos rotos (`.md` y `.lean`, tanto relativos como anclados a la raíz `/...`).
2. 100% de bloques ```lean ... ``` compilables en modo standalone puro (compatible con
   `live.lean-lang.org`), sin `import LeanTT`, con `0 sorry`, `0` errores y `0` warnings,
   replicando exactamente la concatenación de bloques `namespace` previos de `index.html`.
"""

from __future__ import annotations

import concurrent.futures
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import textwrap
from dataclasses import dataclass

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent


def find_lean_binary() -> str:
    # Primero intentamos resolver el binario directo del toolchain activo del repositorio via `elan which lean`
    elan_bin = shutil.which("elan") or str(pathlib.Path.home() / ".elan" / "bin" / "elan")
    if pathlib.Path(elan_bin).is_file():
        try:
            out = subprocess.check_output(
                [elan_bin, "which", "lean"],
                cwd=REPO_ROOT,
                text=True,
                timeout=15,
            ).strip()
            if out and pathlib.Path(out).is_file():
                return out
        except Exception:
            pass
    env_lean = shutil.which("lean")
    if env_lean:
        return env_lean
    home = pathlib.Path.home()
    candidates = [
        home / ".elan" / "toolchains" / "leanprover--lean4---v4.35.0" / "bin" / "lean",
        home / ".elan" / "bin" / "lean",
    ]
    for cand in candidates:
        if cand.is_file():
            return str(cand)
    raise RuntimeError("No se encontró el binario `lean` en PATH ni en ~/.elan.")


FENCE_RE = re.compile(
    r"^(?P<indent>[ \t]*)```(?P<lang>[A-Za-z0-9_-]*)[ \t]*\n(?P<body>.*?)^(?P=indent)```[ \t]*$",
    re.MULTILINE | re.DOTALL,
)

LINK_RE = re.compile(r"!?\[[^\]]*\]\(([^)]+)\)")
OPEN_NS_RE = re.compile(r"^open\s+([A-Za-z0-9_.]+)", re.MULTILINE)
DECL_NS_RE = re.compile(r"^namespace\s+([A-Za-z0-9_.]+)", re.MULTILINE)


def collect_markdown_files() -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for root_md in ("README.md", "_sidebar.md"):
        p = REPO_ROOT / root_md
        if p.is_file():
            files.append(p)
    docs_dir = REPO_ROOT / "docs"
    if docs_dir.is_dir():
        files.extend(sorted(docs_dir.rglob("*.md")))
    return files


def check_markdown_links(md_files: list[pathlib.Path]) -> list[str]:
    errors: list[str] = []
    checked = 0
    for md_path in md_files:
        raw = md_path.read_text(encoding="utf-8")
        # Eliminar bloques cercados y código inline para no inspeccionar ejemplos sintácticos
        stripped = FENCE_RE.sub("", raw)
        stripped = re.sub(r"`[^`\n]+`", "", stripped)
        for match in LINK_RE.finditer(stripped):
            target = match.group(1).strip()
            if not target or target.startswith(("#", "http://", "https://", "mailto:", "javascript:")):
                continue
            clean_path = target.split("#", 1)[0].split("?", 1)[0].strip()
            if not clean_path:
                continue
            if clean_path.startswith("/"):
                resolved = (REPO_ROOT / clean_path.lstrip("/")).resolve()
            else:
                resolved = (md_path.parent / clean_path).resolve()
            checked += 1
            if not resolved.exists():
                rel_src = md_path.relative_to(REPO_ROOT)
                errors.append(f"[ENLACE ROTO] {rel_src} -> '{target}' (no existe {resolved})")
    print(f"✔ Enlaces internos verificados: {checked} enlaces analizados ({len(errors)} errores).")
    return errors


@dataclass
class SnippetJob:
    rel_file: str
    block_idx: int
    start_line: int
    payload: str
    raw_code: str


def extract_lean_snippets(md_files: list[pathlib.Path]) -> tuple[list[SnippetJob], list[str]]:
    jobs: list[SnippetJob] = []
    policy_errors: list[str] = []

    for md_path in md_files:
        if md_path.name == "_sidebar.md":
            continue
        text = md_path.read_text(encoding="utf-8")
        rel_file = str(md_path.relative_to(REPO_ROOT))
        page_namespace_blocks: list[str] = []
        seen_namespaces: set[str] = set()
        lean_idx = 0

        for match in FENCE_RE.finditer(text):
            lang = match.group("lang").strip().lower()
            if lang != "lean":
                continue
            lean_idx += 1
            start_line = text.count("\n", 0, match.start()) + 1
            raw_code = textwrap.dedent(match.group("body")).strip()
            if not raw_code:
                continue

            if re.search(r"^\s*import\s+LeanTT\b", raw_code, re.MULTILINE):
                policy_errors.append(
                    f"[IMPORT PROHIBIDO EN PLAYGROUND] {rel_file}:{start_line} (bloque #{lean_idx}) "
                    "usa `import LeanTT...`, que no existe en live.lean-lang.org."
                )

            open_matches = OPEN_NS_RE.findall(raw_code)
            ns_matches = DECL_NS_RE.findall(raw_code)
            needs_prior = any(ns in seen_namespaces for ns in open_matches) or any(
                ns in seen_namespaces for ns in ns_matches
            )

            payload = raw_code
            if needs_prior and page_namespace_blocks:
                payload = "\n\n".join(page_namespace_blocks) + "\n\n" + raw_code

            jobs.append(
                SnippetJob(
                    rel_file=rel_file,
                    block_idx=lean_idx,
                    start_line=start_line,
                    payload=payload,
                    raw_code=raw_code,
                )
            )

            if ns_matches:
                page_namespace_blocks.append(raw_code)
                seen_namespaces.update(ns_matches)

    return jobs, policy_errors


def verify_single_snippet(lean_bin: str, job: SnippetJob) -> str | None:
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", encoding="utf-8", delete=False) as tmp:
        tmp.write(job.payload + "\n")
        tmp_path = tmp.name

    try:
        # Ejecutamos `lean` fuera del proyecto Lake (cwd=/tmp y sin LEAN_PATH local) para
        # emular con exactitud el entorno standalone del Web Playground oficial.
        env = dict(os.environ)
        env.pop("LEAN_PATH", None)
        try:
            proc = subprocess.run(
                [lean_bin, tmp_path],
                cwd=REPO_ROOT,
                env=env,
                capture_output=True,
                text=True,
                timeout=60,
            )
        except subprocess.TimeoutExpired:
            return f"[TIMEOUT SNIPPET LEAN >60s] {job.rel_file}:{job.start_line} (bloque #{job.block_idx})"
        combined = (proc.stdout or "") + (proc.stderr or "")
        bad_lines = [
            line
            for line in combined.splitlines()
            if ": error:" in line or ": warning:" in line
        ]
        if proc.returncode != 0 or bad_lines:
            cleaned = combined.replace(tmp_path, f"{job.rel_file} (bloque #{job.block_idx}, línea {job.start_line})")
            return f"[FALLO SNIPPET LEAN] {job.rel_file}:{job.start_line} (bloque #{job.block_idx}):\n{cleaned.strip()}"
        return None
    finally:
        try:
            os.remove(tmp_path)
        except OSError:
            pass


def main() -> int:
    lean_bin = find_lean_binary()
    md_files = collect_markdown_files()
    print(f"Usando compilador Lean: {lean_bin}")
    print(f"Archivos Markdown detectados: {len(md_files)}")

    all_errors: list[str] = []
    all_errors.extend(check_markdown_links(md_files))

    jobs, policy_errors = extract_lean_snippets(md_files)
    all_errors.extend(policy_errors)
    print(f"Verificando {len(jobs)} bloques ejecutables ```lean``` en modo Playground standalone...")

    max_workers = min(8, (os.cpu_count() or 4))
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as pool:
        futures = [pool.submit(verify_single_snippet, lean_bin, job) for job in jobs]
        for fut in concurrent.futures.as_completed(futures):
            err = fut.result()
            if err:
                all_errors.append(err)

    if all_errors:
        print("\n❌ Se encontraron errores de validación en la documentación:\n", file=sys.stderr)
        for err in all_errors:
            print(err, file=sys.stderr)
            print("-" * 72, file=sys.stderr)
        print(f"\nTotal de incidencias: {len(all_errors)}", file=sys.stderr)
        return 1

    print(f"✅ ÉXITO TOTAL: {len(jobs)}/{len(jobs)} bloques ```lean``` compilados con 0 errores y 0 warnings.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
