#!/usr/bin/env julia
# SPDX-License-Identifier: Apache-2.0
#
# gen_uniform_LB_18794_lean.jl
#
# Lê Certs/uniform-LB-18794.json e gera RoughBlocks/External/Certs/UniformLB18794.lean
# com uma função Fin 9 → ℚ contendo os finalLowerLo por bloco (x=0..8).
#
# Uso:
#   julia --project=external/julia external/julia/gen_uniform_LB_18794_lean.jl \
#     Certs/uniform-LB-18794.json RoughBlocks/External/Certs/UniformLB18794.lean

using JSON

# ---------- util: transforma "a/b" ou decimal (com expoente) em racional reduzido ----------
function to_rational_strings(s::AbstractString)
    st = strip(String(s))
    if occursin('/', st)
        a, b = split(st, '/')
        num = parse(BigInt, strip(a))
        den = parse(BigInt, strip(b))
        den == 0 && error("denominador zero em \"$s\"")
        g = gcd(num, den); num ÷= g; den ÷= g
        if den < 0; num = -num; den = -den; end
        return string(num), string(den)
    end
    m = match(r"^\s*([+-]?)(\d*)(?:\.(\d*))?(?:[eE]([+-]?\d+))?\s*$", st)
    m === nothing && error("não reconheço literal numérico: \"$s\"")
    sgn   = m.captures[1]
    intp  = something(m.captures[2], "")
    fracp = something(m.captures[3], "")
    expo  = m.captures[4]
    exp10 = expo === nothing ? 0 : parse(Int, expo)
    digits = intp * fracp
    digits == "" && (digits = "0")
    num = parse(BigInt, (sgn == "-" ? "-" : "") * digits)
    den = BigInt(1)
    den *= big(10)^length(fracp)
    if exp10 > 0
        num *= big(10)^exp10
    elseif exp10 < 0
        den *= big(10)^(-exp10)
    end
    g = gcd(num, den); num ÷= g; den ÷= g
    if den < 0; num = -num; den = -den; end
    return string(num), string(den)
end

# pega o valor finalLowerLo "melhor disponível" em cada bloco
function pick_final_q(ent::Dict{String,Any})
    if haskey(ent, "finalLowerLo_q")
        return String(ent["finalLowerLo_q"])
    elseif haskey(ent, "lb_base_lower")
        return String(ent["lb_base_lower"])
    elseif haskey(ent, "LB_at_m_min_interval") && haskey(ent["LB_at_m_min_interval"], "lo")
        return String(ent["LB_at_m_min_interval"]["lo"])
    else
        error("entrada não tem finalLowerLo_q nem lb_base_lower nem LB_at_m_min_interval.lo")
    end
end

function main(injson::String, outlean::String)
    j = JSON.parsefile(injson)
    byx = Dict{Int,Dict{String,Any}}()
    for ent in (j["by_x"]::Vector)
        x = Int(ent["x"])
        byx[x] = ent
    end
    vals = Vector{Tuple{String,String}}(undef, 9)  # (num, den) para x = 0..8
    for x in 0:8
        haskey(byx, x) || error("JSON não contém bloco x=$x")
        qstr = pick_final_q(byx[x])
        num, den = to_rational_strings(qstr)
        vals[x+1] = (num, den)
    end

    io = open(outlean, "w")
    try
        println(io, "-- AUTOGERADO a partir de ", injson, " — não edite manualmente.\n")
        println(io, "import Mathlib\n")
        println(io, "namespace RoughBlocks.External.Certs\n")
        println(io, "/-- finalLowerLo (uniform LB) para m ≥ 18794, por bloco x ∈ Fin 9. -/")
        println(io, "def uniformLB18794_finalLowerLo : Fin 9 → ℚ")
        for x in 0:8
            num, den = vals[x+1]
            print(io, "| ⟨", x, ", _⟩ => ")
            if den == "1"
                println(io, "(", num, " : ℚ)")
            else
                println(io, "(( ", num, " : ℚ) / (", den, " : ℚ))")
            end
        end
        println(io, "\n@[inline] def uniformLB18794_finalLowerLoOf (x : ℕ) (hx : x ≤ 8) : ℚ :=")
        println(io, "  uniformLB18794_finalLowerLo ⟨x, Nat.lt_succ_of_le hx⟩\n")
        println(io, "end RoughBlocks.External.Certs")
    finally
        close(io)
    end
    println("Wrote Lean module to: ", outlean)
end

if abspath(PROGRAM_FILE) == @__FILE__
    if length(ARGS) != 2
        println("""
Usage:
  julia --project=external/julia external/julia/gen_uniform_LB_18794_lean.jl \
    Certs/uniform-LB-18794.json RoughBlocks/External/Certs/UniformLB18794.lean
""")
        exit(1)
    end
    main(ARGS[1], ARGS[2])
end