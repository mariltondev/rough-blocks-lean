# Índice de definições — RoughBlocks v0

## Heavy.Interface
- consts: `C1Default`, `C2Default`, `U0Default`, `BridgeThreshold`, `m0`
- defs auxiliares: `K`, `mRough`, `omega`, `PhiGE`, `PhiDiffAt`

---

## Heavy.LB_Core (Parte 2)
- `def LB_CORE (m x : ℕ) : ℝ` — lado analítico no bloco
- `def margin_CORE (m : ℕ) : ℝ` — cota por ω(u) ≥ 1/3
- `lemma log_pos_of_ge_two_CORE` — log(m) > 0 para m ≥ 2
- `lemma u_block_range_of_ge_U0_CORE` — u ∈ [2,3] para m ≥ U0Default, x ≤ 8
- `lemma LB_ge_margin_CORE'` — LB ≥ margin, uniformemente

---

## External.Certs.UniformLB18794Bridge
- `def PhiDiffAt (m x : ℕ) : ℝ` — diferença Φ em (m, x)
- constantes: `uniformLB18794_finalLowerLo`, `uniformLB18794_finalUpperHi`
- tipos principais: `K`, `mRough`
- objetivo: conectar cotas computacionais e blocos Φ

---

## External.Certs.uniform_bridge_certificate_parte3 (gerado via Julia)
- `def m_min_from_cert : ℕ` — mínimo m do certificado
- `def logm_min_lo_q, logm_min_hi_q : ℚ` — intervalo para log(mₘᵢₙ)
- `def omega_lo_q_from_cert, omega_hi_q_from_cert : Fin 9 → ℚ` — cotas de ω(u)
- `def u_lo_q_from_cert, u_hi_q_from_cert : Fin 9 → ℚ` — cotas de u
- `def omega_lo_from_cert, omega_hi_from_cert, u_lo_from_cert, u_hi_from_cert : Fin 9 → ℝ`

---

## External.Certs.Parte03
- `def uniform_bridge_certificate_parte3_json : String` — JSON canônico do certificado
- `axixom buildPlugFromJSON` — shim provisório para leitura do JSON
- `def Hplug_uniformLB` — plug uniforme (LB ≤ Φ) derivado do certificado

---

## External.Certs.Parte04 (prova final)
- `theorem exists_allNine_ge_m0_using_uniformBridge`
  - enunciado: ∀ m ≥ m₀, ∀ x : Fin 9, ∃ k ∈ K m x, mRough m k
  - usa: `UniformBridgeFrom_m0`, `PhiDiffAt`, `Hplug_uniformLB`
- `theorem exists_allNine_ge_m0_using_uniformBridge_strict`
  - versão com hipóteses explícitas (BridgeThreshold, cotas > 1)
- `theorem exists_allNine_ge_m0_auto_plug_closed_all`
  - versão fechada, usa `buildPlugFromJSON` (a ser substituído pelo verificador real)

---

## External.Certs.AllNine_Framework
- lemmas auxiliares:
  - `exists_mRough_in_block_ge_m0_using_uniformBridge`
  - `one_per_block_ge_m0_using_uniformBridge`
- principais:
  - `exists_allNine_ge_m0_using_uniformBridge`
  - `one_per_block_ge_m0_using_uniformBridge_strict`

---

## Heavy.Numeric (referência)
- `lemma margin_base_1e6`, `lemma margin_mono_from_1e6`
- `theorem margin_ge_one_from_1e6`
- `theorem budget_conservative`
- `theorem budget_main` — unificação das faixas computacional e assintótica

---

## Estrutura geral

- **Parte 1** — constantes e tabelas numéricas (`UniformLB18794Bridge`)
- **Parte 2** — análise e cota LB ≥ margin (`LB_CORE`)
- **Parte 3** — ponte uniforme e certificado (`Hplug_uniformLB`)
- **Parte 4** — fechamento existencial (`∃ k ∈ K m x, mRough m k`)
- **Heavy.Numeric** — faixa assintótica formal (m ≥ 10⁶)
- **BridgeThreshold** — ponto de transição (m₀ = 18794)

---

🧩 **Status**  
Todas as definições Lean listadas acima compilam e estão integradas.  
Restante: substituir o `axixom buildPlugFromJSON` por uma função Lean gerada automaticamente a partir do certificado `.json` (sem axiomas).