/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Std

private def parseNat (o : Option String) (d : Nat) : Nat :=
  match o with
  | some s =>
    match s.toNat? with
    | some n => n
    | none   => d
  | none => d

-- Definição temporária para testar
def countRoughInBlock (m x : Nat) : Nat :=
  match m, x with
  | 0, _ => 0
  | 1, _ => 0
  | _, _ => 1  -- Implementação dummy para teste

/--
Executável simples: computa `countRoughInBlock m x` para um `m,x` pequenos
e imprime o resultado. Você pode passar `m` e `x` na linha de comando.
Ex.:  lake exe roughblocks_scratch 100 0
-/
def main (args : List String) : IO Unit := do
  let m : Nat := parseNat (args[0]?) 100
  let x : Nat := parseNat (args[1]?) 0
  let c := countRoughInBlock m x
  IO.println s!"RoughBlocks scratch"
  IO.println s!"m = {m}, x = {x}"
  IO.println s!"countRoughInBlock(m,x) = {c}"
  IO.println <| if c = 0 then
    "Nenhum m-rough encontrado nesse bloco (para este m pequeno, é normal)."
  else
    "Existe pelo menos um m-rough neste bloco."
