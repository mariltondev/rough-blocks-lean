/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import RoughBlocks.Light.Export
import RoughBlocks.Light.Existence
import RoughBlocks.External.BridgeUniform

/-!
# RoughBlocks.Light.Spec

Módulo de **especificação/checagem** (sentinela de integração).
Não expõe API, não tem efeitos de runtime; apenas força a elaboração
de alvos importantes e imprime a estrutura de dependências.
-/

namespace RoughBlocks.Light.Spec

/-
# Dependency structure — Formal range (Heavy.Numeric)
-/
#eval do
  IO.println ""
  IO.println "==================================================================="
  IO.println "RoughBlocks — Dependency Structure (Formal Range / Heavy.Numeric)"
  IO.println "==================================================================="
  IO.println ""

#eval IO.println " (1) margin_ge_one_at_1e6 — base case (formal)"
#print axioms RoughBlocks.Heavy.Numeric.margin_ge_one_at_1e6
#eval IO.println "-------------------------------------------------------------------"

#eval IO.println " (2) margin_ge_one_from_1e6 — monotonic propagation"
#print axioms RoughBlocks.Heavy.Numeric.margin_ge_one_from_1e6
#eval IO.println "-------------------------------------------------------------------"

#eval IO.println " (3) budget_conservative_formal — LB ≥ 1 for m ≥ 10^6"
#print axioms RoughBlocks.Heavy.Numeric.budget_conservative_formal
#eval IO.println "-------------------------------------------------------------------"
#eval IO.println ""

/-
# Dependency structure — Light layer (public-facing)
-/
#eval do
  IO.println ""
  IO.println "==================================================================="
  IO.println "RoughBlocks — Dependency Structure (Light Layer)"
  IO.println "==================================================================="
  IO.println ""

#eval IO.println " of_block_to_interval_primes — block → interval + prime condition"
#print axioms RoughBlocks.Light.of_block_to_interval_primes
#eval IO.println "-------------------------------------------------------------------"

#eval IO.println " exist_in_block_ge_1e6_if_bridge — existence with direct bridge"
#print axioms RoughBlocks.Light.exist_in_block_ge_1e6_if_bridge
#eval IO.println "-------------------------------------------------------------------"

#eval IO.println " existence_ge_1e6_uniform — uses uniform external bridge"
#print axioms RoughBlocks.Light.existence_ge_1e6_uniform
#eval IO.println "-------------------------------------------------------------------"

#eval IO.println " existence_main_all — unified theorem (m ≥ 2)"
#print axioms RoughBlocks.Light.existence_main_all
#eval IO.println "-------------------------------------------------------------------"
#eval IO.println ""

/-
# External artifacts (explicit)
-/
#eval IO.println " External axiom: bridge_ge_1e6_uniform (JSON-based uniform bridge)"
#print axioms RoughBlocks.External.bridge_ge_1e6_uniform
#eval IO.println "-------------------------------------------------------------------"

#eval IO.println " External axiom: budget_verified_by_scan (Zenodo deterministic scan)"
#print axioms RoughBlocks.Light.budget_verified_by_scan
#eval IO.println "-------------------------------------------------------------------"

end RoughBlocks.Light.Spec
