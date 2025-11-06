# generate_lean_uniform_bridge_increment_1e6.jl
# Converte certs/uniform-bridge-increment-1e6.json em UniformGE1e6Bridge.lean
# Uso:
#   CERT_JSON=certs/uniform-bridge-increment-1e6.json \
#   LEAN_OUT=RoughBlocks/External/Certs/UniformGE1e6Bridge.lean \
#   [LOWER_BOUND_LEMMA=RoughBlocks.Heavy.WindowLink.Block.window_link_row0_1e6] \
#   [STRICT_DELTA=1] \
#   julia --project=. external/julia/generate_lean_uniform_bridge_increment_1e6.jl

using JSON

# ---------------- util: converter string "num//den" ou decimal -> literal Lean em ℚ ----------------
function dec_to_rat_lean(s::String)
    # já racionalizado "num//den"
    if occursin("//", s)
        parts = split(s, "//")
        length(parts) == 2 || error("Formato racional inválido: $s")
        num = strip(parts[1]); den = strip(parts[2])
        return "((" * num * " : ℚ) / (" * den * " : ℚ))"
    end
    # inteiro puro
    if !occursin(".", s)
        return "(" * s * " : ℚ)"
    end
    # decimal finito (sem notação científica)
    if occursin("e", lowercase(s)) || occursin("E", s)
        error("Formato científico não suportado: $s")
    end
    parts = split(s, ".")
    length(parts) == 2 || error("Decimal inválido: $s")
    intp, frac = parts[1], parts[2]
    sign = startswith(intp, "-") ? "-" : ""
    intp = replace(intp, "-" => "")
    if all(c -> c == '0', frac)
        return "(" * sign * intp * " : ℚ)"
    end
    num = replace(intp * frac, r"^0+" => "")
    num = isempty(num) ? "0" : num
    pow = string(length(frac))
    num_expr = sign * num
    return "((" * num_expr * " : ℚ) / (10^" * pow * " : ℚ))"
end

# ---------------- impressão do bloco rows1e6 ----------------
function write_rows1e6(io, byx)
    println(io, "def rows1e6 : List BridgeRow := [")
    for (i, blk) in enumerate(byx)
        x  = blk["x"]
        u  = blk["u_interval_q"]; w = blk["omega_interval_q"]
        uLo = dec_to_rat_lean(u["lo"]);   uHi = dec_to_rat_lean(u["hi"])
        wLo = dec_to_rat_lean(w["lo"]);   wHi = dec_to_rat_lean(w["hi"])
        tMainLo = dec_to_rat_lean(blk["t_main_lo_q"])
        m2Lo    = dec_to_rat_lean(blk["m2_lo_q"])
        rLo     = dec_to_rat_lean(blk["r_lo_q"])
        e1Up    = dec_to_rat_lean(blk["e1_up_q"])
        e2      = dec_to_rat_lean(blk["e2_q"])
        finalLo = dec_to_rat_lean(blk["final_lower_lo_q"])
        lbHi    = dec_to_rat_lean(blk["lb_hi_q"])
        dLo     = dec_to_rat_lean(blk["delta_lo_q"])
        print(io, "  { x := ", x,
              ", uLo := ", uLo, ", uHi := ", uHi,
              ", omegaLo := ", wLo, ", omegaHi := ", wHi,
              ", tMainLo := ", tMainLo, ", m2Lo := ", m2Lo, ", rLo := ", rLo,
              ", e1Up := ", e1Up, ", e2 := ", e2,
              ", finalLowerLo := ", finalLo, ", lbHi := ", lbHi, ", deltaLo := ", dLo, " }")
        if i < length(byx)
            println(io, ",")
        else
            println(io)
        end
    end
    println(io, "]\n")
end

# ---------------- gera cabeçalho Lean ----------------
function write_header(io)
    println(io, "import Mathlib")
    println(io, "import RoughBlocks.Heavy.WindowLink.Block")
    println(io, "")
    println(io, "noncomputable section")
    println(io, "namespace RoughBlocks.External.Certs.UniformGE1e6Bridge")
    println(io, "")
    println(io, "open RoughBlocks RoughBlocks.Heavy")
    println(io, "")
    println(io, "structure BridgeRow where")
    println(io, "  x : ℕ")
    println(io, "  uLo : ℚ")
    println(io, "  uHi : ℚ")
    println(io, "  omegaLo : ℚ")
    println(io, "  omegaHi : ℚ")
    println(io, "  tMainLo : ℚ")
    println(io, "  m2Lo : ℚ")
    println(io, "  rLo : ℚ")
    println(io, "  e1Up : ℚ")
    println(io, "  e2 : ℚ")
    println(io, "  finalLowerLo : ℚ")
    println(io, "  lbHi : ℚ")
    println(io, "  deltaLo : ℚ")
    println(io, "")
end

function write_helpers(io; strict_delta::Bool=false)
    println(io, "/-- Seleciona a linha `rows1e6` para `x ≤ 8`. -/")
    println(io, "def row1e6Of (x : ℕ) (hx : x ≤ 8) : BridgeRow := by")
    println(io, "  have hlen : rows1e6.length = 9 := by simp [rows1e6]")
    println(io, "  have hxlt : x < rows1e6.length := by")
    println(io, "    simpa [hlen] using Nat.lt_of_le_of_lt hx (by decide : 8 < 9)")
    println(io, "  exact rows1e6.get ⟨x, hxlt⟩")
    println(io, "")
    println(io, "/-- A linha do certificado para x = 0. -/")
    println(io, "def row0 : BridgeRow := row1e6Of 0 (by decide)")
    println(io, "")
    println(io, "/-- Resíduo assinado do balanço (LHS - RHS). -/")
    println(io, "def computeDelta (r : BridgeRow) : ℚ :=")
    println(io, "  r.tMainLo - r.e1Up - r.e2 - r.uHi - r.omegaHi + r.m2Lo + r.rLo - r.finalLowerLo")
    println(io, "")
    println(io, "/-- Checagem booleana da linha (verificador estrutural). -/")
    if strict_delta
        # Igualdade do resíduo (use só se sabe que o JSON traz igualdade exata).
        println(io, "def checkRow (r : BridgeRow) : Bool :=")
        println(io, "  decide (r.uLo ≤ r.uHi) &&")
        println(io, "  decide (r.omegaLo ≤ r.omegaHi) &&")
        println(io, "  decide (r.finalLowerLo ≤ r.lbHi) &&") # ← direção CORRETA
        println(io, "  decide (computeDelta r = r.deltaLo)")
        println(io, "")
        println(io, "def CheckRowProp (r : BridgeRow) : Prop :=")
        println(io, "  r.uLo ≤ r.uHi ∧ r.omegaLo ≤ r.omegaHi ∧")
        println(io, "  r.finalLowerLo ≤ r.lbHi ∧")
        println(io, "  computeDelta r = r.deltaLo")
    else
        # Tolerante: computeDelta ≤ deltaLo (recomendado como default).
        println(io, "def checkRow (r : BridgeRow) : Bool :=")
        println(io, "  decide (r.uLo ≤ r.uHi) &&")
        println(io, "  decide (r.omegaLo ≤ r.omegaHi) &&")
        println(io, "  decide (r.finalLowerLo ≤ r.lbHi) &&") # ← direção CORRETA
        println(io, "  decide (computeDelta r ≤ r.deltaLo)")
        println(io, "")
        println(io, "def CheckRowProp (r : BridgeRow) : Prop :=")
        println(io, "  r.uLo ≤ r.uHi ∧ r.omegaLo ≤ r.omegaHi ∧")
        println(io, "  r.finalLowerLo ≤ r.lbHi ∧")
        println(io, "  computeDelta r ≤ r.deltaLo")
    end
    println(io, "")
    println(io, "@[simp] theorem checkRow_iff (r : BridgeRow) : checkRow r = true ↔ CheckRowProp r := by")
    println(io, "  simp [checkRow, CheckRowProp, Bool.and_eq_true, decide_eq_true_eq, and_assoc]")
    println(io, "")
end

# ---------------- lemas para row0: final=lbHi e suas coerções ----------------
function write_row0_lbhi_lemmas(io)
    println(io, "/-- Em `x=0`, os literais indicam `lbHi = finalLowerLo` (em ℚ). -/")
    println(io, "@[simp] lemma row0_lbHi_eq_final_q : (row0.lbHi : ℚ) = row0.finalLowerLo := by")
    println(io, "  simp [row0, row1e6Of, rows1e6]")
    println(io, "")
    println(io, "/-- Consequência: `finalLowerLo ≤ lbHi` (em ℚ). -/")
    println(io, "lemma row0_final_le_lbHi_q : row0.finalLowerLo ≤ (row0.lbHi : ℚ) := by")
    println(io, "  simpa [row0_lbHi_eq_final_q]")
    println(io, "")
    println(io, "/-- E a versão em ℝ, via coerção. -/")
    println(io, "lemma row0_final_le_lbHi_real : (row0.finalLowerLo : ℝ) ≤ (row0.lbHi : ℝ) := by")
    println(io, "  exact_mod_cast row0_final_le_lbHi_q")
    println(io, "")
end

# ---------------- lemma row0_finalLowerLo_q e ge_one_real (versão enxuta) ----------------
function write_row0_literals_lemmas(io, final_lo_q::String)
    parts = split(final_lo_q, "//")
    length(parts) == 2 || error("final_lower_lo_q não está em formato num//den")
    num = strip(parts[1]); den = strip(parts[2])

    println(io, "/-- Forma fechada (em ℚ) de `row0.finalLowerLo` como fração `N/D`. -/")
    println(io, "lemma row0_finalLowerLo_q :")
    println(io, "  (row0.finalLowerLo : ℚ) =")
    println(io, "    ((" * num * " : ℚ) / (" * den * " : ℚ)) := by")
    println(io, "  simp [row0, row1e6Of, rows1e6]")
    println(io, "")

    println(io, "/-- Fato numérico: a linha 0 dá `finalLowerLo ≥ 1` (em ℝ). -/")
    println(io, "lemma row0_finalLowerLo_ge_one_real : (row0.finalLowerLo : ℝ) ≥ (1 : ℝ) := by")
    println(io, "  -- Prova em ℚ com `one_le_div_iff` (sem argumentos), depois coerção para ℝ.")
    println(io, "  have hq : (1 : ℚ) ≤ (row0.finalLowerLo : ℚ) := by")
    println(io, "    set N : ℚ := (" * num * " : ℚ)")
    println(io, "    set D : ℚ := (" * den * " : ℚ)")
    println(io, "    have hDpos : (0 : ℚ) < D := by dsimp [D]; decide")
    println(io, "    have hD_le_N : D ≤ N := by dsimp [N, D]; decide")
    println(io, "    -- Forma geral de `one_le_div_iff` e escolha do caso `D > 0`.")
    println(io, "    have hiff :")
    println(io, "      (1 : ℚ) ≤ N / D ↔ (0 < D ∧ D ≤ N) ∨ (D < 0 ∧ N ≤ D) := one_le_div_iff")
    println(io, "    have hcase : (0 < D ∧ D ≤ N) ∨ (D < 0 ∧ N ≤ D) := Or.inl ⟨hDpos, hD_le_N⟩")
    println(io, "    have h : (1 : ℚ) ≤ N / D := Iff.mpr hiff hcase")
    println(io, "    simpa [row0_finalLowerLo_q, N, D] using h")
    println(io, "  exact_mod_cast hq")
    println(io, "")
end

# ---------------- lemma opcional: row0_count_ge_finalLowerLo_1e6 ----------------
function write_row0_bound_lemma(io; lower_bound_lemma::Union{Nothing,String}=nothing)
    println(io, "/-- Lema numérico (x = 0): bound direto de janela curta para m ≥ 1e6. -/")
    println(io, "lemma row0_count_ge_finalLowerLo_1e6")
    println(io, "  {m : ℕ} (hm : 1000000 ≤ m) :")
    println(io, "  (countRoughInBlock m 0 : ℝ) ≥ (row0.finalLowerLo : ℝ) :=")
    if lower_bound_lemma === nothing || isempty(lower_bound_lemma)
        println(io, "by")
        println(io, "  -- Substitua este `admit` por sua prova numérica (pipeline).")
        println(io, "  admit")
    else
        println(io, "by")
        println(io, "  -- Usa o lema fornecido via pipeline (wrapper no Block.lean).")
        println(io, "  -- Ele retorna o bound com o literal NUM/DEN; aqui reescrevemos por `row0_finalLowerLo_q`.")
        println(io, "  have h := " * lower_bound_lemma * " (m := m) hm")
        println(io, "  simpa [row0_finalLowerLo_q] using h")
    end
    println(io, "")
end

# ---------------- escrever footer ----------------
function write_footer(io)
    println(io, "end RoughBlocks.External.Certs.UniformGE1e6Bridge")
end

# ---------------- main ----------------
function main()
    json_in  = get(ENV, "CERT_JSON", "certs/uniform-bridge-increment-1e6.json")
    lean_out = get(ENV, "LEAN_OUT", "RoughBlocks/External/Certs/UniformGE1e6Bridge.lean")
    lb_lemma = get(ENV, "LOWER_BOUND_LEMMA", "")
    strict   = get(ENV, "STRICT_DELTA", "1")  # padrão: estrito
    strict_delta = lowercase(strict) in ("1","true","t","yes","y")

    cert = JSON.parsefile(json_in)
    byx = cert["by_x"]
    # capturar o final_lower_lo da linha x=0 para construir o lema ge_one_real
    row0 = nothing
    for blk in byx
        if blk["x"] == 0
            row0 = blk
            break
        end
    end
    row0 === nothing && error("Bloco x=0 não encontrado no JSON")

    open(lean_out, "w") do io
        write_header(io)
        write_rows1e6(io, byx)
        write_helpers(io; strict_delta=strict_delta)
        write_row0_lbhi_lemmas(io)
        write_row0_literals_lemmas(io, row0["final_lower_lo_q"])
        write_row0_bound_lemma(io; lower_bound_lemma = isempty(lb_lemma) ? nothing : lb_lemma)
        write_footer(io)
    end
    println("Wrote Lean bridge to: $lean_out")
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end