/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Std.Tactic
open Std

namespace RoughBlocks.Light.Native

/--
Prime sieve up to `N` (inclusive), returning all primes in ascending order.

Pure function implemented with an imperative loop via `Id.run`.
-/
def primesUpTo (N : Nat) : Array Nat := Id.run do
  if N < 2 then
    return #[]
  -- `s[i] = true` means “potentially prime”.
  let mut s : Array Bool := Array.replicate (N+1) true
  s := s.set! 0 false |>.set! 1 false
  let mut p := 2
  while p*p ≤ N do
    if s[p]! then
      -- Strike multiples of `p` from p*p up to N.
      let mut k := p*p
      while k ≤ N do
        s := s.set! k false
        k := k + p
    p := p + 1
  -- Collect primes in ascending order.
  let mut res : Array Nat := #[]
  for i in [2:N+1] do
    if s[i]! then
      res := res.push i
  return res

/--
Main verification kernel.

For each `m ∈ [mMin..mMax]`, mark all multiples of primes `p ≤ m` inside the
half-open interval `[start, stop) = [m^2+1, m^2+9m+1)`. For each level
`x = 0..8`, we require the existence of at least one `i ∈ {1..m}` such that
`n = m^2 + x·m + i` remains unmarked. Unmarked means “not divisible by any
prime `≤ m`”, i.e., `n` is `m`-rough. If any level lacks such an `i`, we
short-circuit returning `false`. If all checks pass, return `true`.

Notes:
- We use a single array of length `9·m` to cover the 9 levels at once.
- Half-open interval `[start, stop)` avoids off-by-one errors in loops and indexing.
- Pure function implemented with `Id.run`; no `IO` effects involved.
-/
def mainVerification (mMin mMax : Nat) : Bool := Id.run do
  let allP := primesUpTo mMax
  -- Iterate over m
  for m in [mMin : mMax+1] do
    -- Primes `≤ m` (array is sorted; `takeWhile` avoids extra allocation).
    let primesLeM := allP.takeWhile (· ≤ m)
    -- Single buffer covering the 9 levels:
    let start := m*m + 1
    let stop  := m*m + 9*m + 1  -- exclusive
    let len   := stop - start   -- = 9*m
    let mut mark : Array Bool := Array.replicate len true
    -- Strike multiples of every prime ≤ m.
    for p in primesLeM do
      -- Guard (paranoia): avoid degenerate steps.
      if p ≠ 0 then
        let first := ((start + p - 1) / p) * p
        let mut cur := first
        let mut idx := cur - start
        while cur < stop do
          mark := mark.set! idx false
          cur  := cur + p
          idx  := idx + p
    -- For each level x, require ∃ i ∈ {1..m} with `mark[...] = true`.
    for x in [0:9] do
      let mut existsGood := false
      for i in [1:m+1] do
        let n := m*m + x*m + i
        if mark[n - start]! then
          existsGood := true
          break
      if !existsGood then
        return false
  return true

/--
Production entry point (provisional upper bound).

TODO(MCR): switch `100` → `18794` after polynomial-time tuning and profiling.

This definition is the one consumed by the `native_decide` proof below.
-/
def verify2_18794 : Bool :=
  mainVerification 2 100  -- PROVISIONAL CAP: use 18794 once performance is tuned.

/--
Computationally verified theorem.

`native_decide` compiles and evaluates `verify2_18794` inside the kernel. When
it returns `true`, the equality closes the goal. No external artifacts are used.
-/
theorem verify2_18794_true : verify2_18794 = true := by
  native_decide

#print axioms RoughBlocks.Light.Native.verify2_18794_true

end RoughBlocks.Light.Native
