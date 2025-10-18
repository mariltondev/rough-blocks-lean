#!/usr/bin/env bash
# ci-local.sh — replica os passos do CI localmente
# Uso:
#   chmod +x ./scripts/ci-local.sh        # torna executável
#   ./scripts/ci-local.sh                 # roda light + heavy (heavy é best-effort)
#   ./scripts/ci-local.sh --light         # só a camada Light
#   ./scripts/ci-local.sh --heavy         # só a camada Heavy (não recomendado)
#   ./scripts/ci-local.sh --no-cache      # pula 'lake exe cache get'
#   ./scripts/ci-local.sh --no-scratch    # não roda o executável de demo

set -euo pipefail

# -----------------------------
# opções
DO_LIGHT=1
DO_HEAVY=1
DO_CACHE=1
DO_SCRATCH=1
for arg in "$@"; do
  case "$arg" in
    --light) DO_HEAVY=0 ;;
    --heavy) DO_LIGHT=0 ;;
    --no-cache) DO_CACHE=0 ;;
    --no-scratch) DO_SCRATCH=0 ;;
    *) echo "Unknown flag: $arg" >&2; exit 2 ;;
  esac
done

# -----------------------------
# helpers
GREEN='\033[0;32m'; YELLOW='\033[0;33m'; RED='\033[0;31m'; NC='\033[0m'
info () { echo -e "${YELLOW}==>${NC} $*"; }
ok   () { echo -e "${GREEN}✓${NC} $*"; }
warn () { echo -e "${YELLOW}⚠${NC} $*"; }
err  () { echo -e "${RED}✗${NC} $*"; }

# garantir que estamos na raiz do repo (onde tem lakefile.lean)
cd "$(git rev-parse --show-toplevel 2>/dev/null || pwd)"

command -v lake >/dev/null || { err "lake não encontrado no PATH"; exit 1; }

# -----------------------------
# cache (opcional)
if [[ "$DO_CACHE" -eq 1 ]]; then
  info "Fetching mathlib cache (tolerante a falhas)…"
  lake exe cache get || true
fi

# -----------------------------
# LIGHT (obrigatório)
if [[ "$DO_LIGHT" -eq 1 ]]; then
  info "Building LIGHT artefacts…"

  # ordem sugerida: base da raiz → externo → fachada Light
  light_targets=(
    RoughBlocks.Defs
    RoughBlocks.Check
    RoughBlocks.External.BridgeUniform
    RoughBlocks.Light.Export
    RoughBlocks.Light.Existence
    RoughBlocks.Light.Spec
    RoughBlocks.Light.Concrete
  )
  for tgt in "${light_targets[@]}"; do
    info "lake build ${tgt}"
    lake build "${tgt}"
  done
  ok "Light build ok."

  if [[ "$DO_SCRATCH" -eq 1 ]]; then
    if lake build RoughBlocks.Scratch >/dev/null 2>&1; then
      info "Running scratch demo…"
      if lake exe roughblocks_scratch >/dev/null 2>&1; then
        lake exe roughblocks_scratch
        ok "Scratch demo ok."
      else
        warn "Executável 'roughblocks_scratch' não encontrado (ok se não definido)."
      fi
    else
      warn "RoughBlocks.Scratch não compilou (ok se não existir)."
    fi
  else
    info "Pulando scratch (--no-scratch)."
  fi

  info "Checking for sorry/admit…"
  if grep -R --include='*.lean' -nE '\b(sorry|admit)\b' RoughBlocks >/tmp/lean_sorries.txt 2>/dev/null; then
    cat /tmp/lean_sorries.txt
    err "Found sorry/admit — failing light step."
    exit 1
  fi
  ok "No sorry/admit found."
fi

# -----------------------------
# HEAVY (best-effort; não falha o script)
if [[ "$DO_HEAVY" -eq 1 ]]; then
  info "Building HEAVY modules (best-effort)…"
  HEAVY_FAILED=0
  heavy_targets=(
    RoughBlocks.Heavy.Identity
    RoughBlocks.Heavy.Log10Bounds
    RoughBlocks.Heavy.Buchstab
    RoughBlocks.Heavy.Buchstab.Core
    RoughBlocks.Heavy.Buchstab.MinFac
    RoughBlocks.Heavy.WindowLink.Core
    RoughBlocks.Heavy.WindowLink.Block
    RoughBlocks.Heavy.Bridge
    RoughBlocks.Heavy.Omega
    RoughBlocks.Heavy.Numeric
    RoughBlocks.Heavy.Interface
  )
  for tgt in "${heavy_targets[@]}"; do
    info "lake build ${tgt}"
    if lake build "${tgt}"; then
      ok "${tgt} built."
    else
      warn "${tgt} failed (continuing due to best-effort)."
      HEAVY_FAILED=1
    fi
  done
  if [[ "$HEAVY_FAILED" -eq 1 ]]; then
    warn "Some heavy modules failed. (Isso é esperado no best-effort.)"
  else
    ok "All heavy modules built."
  fi
fi

ok "CI-local completed."