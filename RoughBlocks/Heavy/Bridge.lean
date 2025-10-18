/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.Numeric

noncomputable section
open Classical
open Finset
open RoughBlocks

namespace RoughBlocks.Heavy

/-!
# RoughBlocks.Heavy.Bridge

Camada **ponte** entre o lado analítico e o lado discreto.

A ideia é encapsular o padrão:
\[
  \text{(i) } \mathrm{LB}(m,x) \ge 1
  \quad\text{e}\quad
  \text{(ii) } (\text{contagem no bloco}) \;\ge\; \mathrm{LB}(m,x)
  \;\Longrightarrow\; \text{contagem} \ge 1 \;\Longrightarrow\; \exists\text{ elemento } m\text{-áspero}.
\]

O arquivo fornece:

* `count_ge_one_of_LB_ge_one` — promove “LB ≥ 1” e “contagem ≥ LB” para
  “contagem ≥ 1” em `ℕ`;
* `exists_in_block_of_LB_ge_one` — versão existencial, usando o lema acima;
* `LB_le_count_block` — forma **modular** de “LB ≤ contagem” quando se tem:
  1) um **lema local analítico** que dá uma cota inferior para uma diferença
     de `Φ` em `ℝ`, e
  2) a **identidade de janela** que iguala a contagem no bloco `K m x` a essa
     diferença de `Φ` (com os parâmetros apropriados).

## Escopo e dependências

* Não introduz axiomas.
* Apenas raciocínio elementar com ordens e coerções `ℕ → ℝ`.
* O parâmetro `PhiGE : ℕ → ℕ → ℝ` em `LB_le_count_block` é **abstrato** de propósito:
  este módulo não fixa como a diferença de `Φ` é produzida; ele só encadeia
  “cota analítica ≥ LB” com “contagem = diferença”, resultando em `LB ≤ contagem`.
  A ligação concreta “janela ↔ diferença de `Φ`” fica em módulos especializados.

## Uso típico

1. Obter um lema analítico do tipo
   `((PhiGE (X+Y) p : ℝ) - (PhiGE X p : ℝ)) ≥ LB m x`.
2. Usar a identidade de janela para reescrever
   `(countRoughInBlock m x : ℝ) = (PhiGE (X+Y) p - PhiGE X p : ℝ)`.
3. Aplicar `LB_le_count_block` ⇒ `(LB m x : ℝ) ≤ count`.
4. Combinar com um resultado do tipo `LB m x ≥ 1` ⇒ `count ≥ 1` ⇒ existência no bloco.

As hipóteses `_hm` e `_hx` em `LB_le_count_block` aparecem para manter
uniformidade de assinatura com o restante do projeto (e para futura extensão),
mas **não são usadas** neste lema específico.
-/

/-- **Passo contagem ≥ 1 (versão numérica → natural).**
Se `LBf m x ≥ 1` e `(count : ℝ) ≥ LBf m x`, então a contagem no bloco
`countRoughInBlock m x` é pelo menos `1` em `ℕ`. -/
theorem count_ge_one_of_LB_ge_one
  (LBf : ℕ → ℕ → ℝ) (m x : ℕ)
  (hLB_ge_one : LBf m x ≥ (1 : ℝ))
  (hCount_ge_LB : (countRoughInBlock m x : ℝ) ≥ LBf m x)
  : countRoughInBlock m x ≥ 1 := by
  have hR : (1 : ℝ) ≤ (countRoughInBlock m x : ℝ) := le_trans hLB_ge_one hCount_ge_LB
  exact (by exact_mod_cast hR : 1 ≤ countRoughInBlock m x)

/-- **Existência no bloco a partir de `LB ≥ 1`.**
De `LBf m x ≥ 1` e `(count : ℝ) ≥ LBf m x` segue `∃ n ∈ K m x, mRough m n`. -/
theorem exists_in_block_of_LB_ge_one
  (LBf : ℕ → ℕ → ℝ) (m x : ℕ)
  (hLB_ge_one : LBf m x ≥ (1 : ℝ))
  (hCount_ge_LB : (countRoughInBlock m x : ℝ) ≥ LBf m x)
  : ∃ n ∈ K m x, mRough m n := by
  have h1 : countRoughInBlock m x ≥ 1 :=
    count_ge_one_of_LB_ge_one LBf m x hLB_ge_one hCount_ge_LB
  exact RoughBlocks.exists_of_count_ge_one h1

/-- **Ponte modular `LB ≤ contagem` no bloco `K m x`.**

**Hipóteses (já em `ℝ`):**
* `hPhiDiff_ge_LB` :
  \[
  \bigl(\PhiGE(X{+}Y,m) - \PhiGE(X,m)\bigr) \;\ge\; \mathrm{LB}(m,x),
  \quad \text{com } X = m^2 + x m,\; Y = m;
  \]
* `hCountEq` :
  \[
  (\mathrm{countRoughInBlock}(m,x) : \mathbb{R}) \;=\; \PhiGE(X{+}Y,m) - \PhiGE(X,m),
  \]
  isto é, a identidade de janela que identifica a contagem do bloco com a
  diferença de `Φ`.

**Conclusão:** \((\mathrm{LB}(m,x) : \mathbb{R}) \le (\mathrm{countRoughInBlock}(m,x) : \mathbb{R}).\)

Observação: os parâmetros `_hm` e `_hx` são mantidos por consistência de interface,
embora não sejam usados neste encadeamento. -/
theorem LB_le_count_block
  (PhiGE : ℕ → ℕ → ℝ)
  (m x : ℕ) (_hm : 2 ≤ m) (_hx : x ≤ 8)
  (hPhiDiff_ge_LB :
      (PhiGE (m*m + x*m + m) m - PhiGE (m*m + x*m) m : ℝ) ≥ RoughBlocks.Heavy.Numeric.LB m x)
  (hCountEq :
      (RoughBlocks.countRoughInBlock m x : ℝ)
        = (PhiGE (m*m + x*m + m) m - PhiGE (m*m + x*m) m : ℝ))
  : (RoughBlocks.Heavy.Numeric.LB m x : ℝ) ≤ (RoughBlocks.countRoughInBlock m x : ℝ) := by
  have : (RoughBlocks.Heavy.Numeric.LB m x : ℝ)
            ≤ (PhiGE (m*m + x*m + m) m - PhiGE (m*m + x*m) m : ℝ) := by
    simpa [ge_iff_le] using hPhiDiff_ge_LB
  simpa [hCountEq] using this

end RoughBlocks.Heavy
end
