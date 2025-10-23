#!/usr/bin/env julia
# SPDX-License-Identifier: Apache-2.0
#
# uniform_bridge_LB_18794.jl
#
# Gera um certificado "uniform_LB_certificate" para m ≥ 18794 e x ∈ {0,…,8}.
# - Parte 1 (domínio): u-range e ω(u)-range por intervalos (rigoroso).
# - Parte 2 (base):
#     (A) --final-from-lb   → define finalLowerLo[x] := prevfloat(inf(LB_simp(m_min,x))) e marca lb_base_ok=true
#     (B) arquivo JSON dado → checa LB_simp(m_min,x) ≥ finalLowerLo[x] (lb_base_ok true/false) e grava lb_base_lower
#
# Uso:
#   # Opção A (recomendada): gera finalLowerLo a partir do LB em m_min
#   julia --project=external/julia external/julia/uniform_bridge_LB_18794.jl Certs/uniform-LB-18794.json --pbits=256 --final-from-lb
#
#   # Opção B: valida contra um arquivo com finalLowerLo
#   julia --project=external/julia external/julia/uniform_bridge_LB_18794.jl Certs/uniform-LB-18794.json Certs/rows18794_finalLowerLo.json --pbits=256
#
# Formato opcional de rows18794_finalLowerLo.json:
#   { "0":"<rat>", "1":"<rat>", ..., "8":"<rat>" }
# onde <rat> é "a/b" ou decimal (ex.: "1.2345e-3").

using IntervalArithmetic
import IntervalArithmetic: interval
using JSON

# -------------------------- Auxiliar: parsing numérico --------------------------

function parse_bigfloat_rat(s::AbstractString; pbits::Int=256)
    setprecision(BigFloat, pbits)
    if occursin('/', s)
        a, b = split(s, '/')
        return parse(BigFloat, a) / parse(BigFloat, b)
    else
        return parse(BigFloat, s)
    end
end

# -------------------------- ω(u) em [1,3] (peça-a-peça) ------------------------

function omega_I(uI::Interval{BigFloat})
    one  = big(1); two = big(2); three = big(3)
    oneI = interval(one, one)
    lo, hi = inf(uI), sup(uI)
    if hi < one || lo > three
        error("omega_I: domínio fora de [1,3]: u ∈ $uI")
    end
    parts = Interval{BigFloat}[]
    # [1,2]
    lo12 = max(lo, one);  hi12 = min(hi, two)
    if lo12 <= hi12
        push!(parts, interval(lo12, hi12))
    end
    # [2,3]
    lo23 = max(lo, two);  hi23 = min(hi, three)
    if lo23 <= hi23
        push!(parts, interval(lo23, hi23))
    end
    res = nothing
    for part in parts
        val = if sup(part) <= two
            interval(1,1) / part
        else
            (oneI + log(part - oneI)) / part
        end
        res = isnothing(res) ? val : hull(res, val)
    end
    return res === nothing ? NaN..NaN : res
end

# -------------------------- u-range uniforme (m ≥ 18794) -----------------------

# u(m,x) = log(m^2 + x m) / log m
function u_range_uniform(x::Int; m_min::Int=18794, pbits::Int=256)
    setprecision(BigFloat, pbits)
    m0 = BigFloat(m_min)
    X  = m0*m0 + BigFloat(x)*m0
    u_at_m0 = log(interval(X, X)) / log(interval(m0, m0))
    u_hi = sup(u_at_m0)
    u_lo = big(2)  # limite inferior quando m→∞
    return interval(u_lo, u_hi)
end

# -------------------------- LB_simp intervalar no ponto exato m ----------------

const C1 = big(4.4)
const C2 = big(100)

function LB_interval_at(m::Int, x::Int; pbits::Int=256)
    setprecision(BigFloat, pbits)
    mI = interval(BigFloat(m), BigFloat(m))
    logmI = log(mI)
    uI = log(mI*mI + interval(BigFloat(x), BigFloat(x))*mI) / logmI
    ωI = omega_I(uI)
    term_main = (mI / logmI) * ωI
    term_c1   = C1 * (mI / (logmI^2))
    LB_I = term_main - term_c1 - C2
    return LB_I
end

# -------------------------- Serialização helpers -------------------------------

to_dec(o) = string(o)

function interval_to_dict(I::Interval{BigFloat})
    return Dict("lo" => to_dec(inf(I)), "hi" => to_dec(sup(I)))
end

# -------------------------- Main ----------------------------------------------

function main(outpath::String; pbits::Int=256,
              final_lo_file::Union{Nothing,String}=nothing,
              m_min::Int=18794,
              final_from_lb::Bool=false)
    setprecision(BigFloat, pbits)

    # Domínio: log(m_min)
    logm_min  = log(interval(BigFloat(m_min), BigFloat(m_min)))
    domain    = Dict{String,Any}()
    domain["m_min"]   = string(m_min)
    domain["x_range"] = Dict("lo"=>"0","hi"=>"8")
    domain["logm_min_interval"] = interval_to_dict(logm_min)

    # Opcional (B): carregar finalLowerLo[x] de arquivo
    finalLowerLo = Dict{Int,BigFloat}()
    have_final   = false
    if final_lo_file !== nothing
        txt = read(final_lo_file, String)
        jobj = JSON.parse(txt)
        for x in 0:8
            s = jobj[string(x)]
            s === nothing && error("Arquivo $(final_lo_file) não tem chave \"$x\".")
            finalLowerLo[x] = parse_bigfloat_rat(s; pbits=pbits)
        end
        have_final = true
    end

    # Se vieram os dois (arquivo + flag), a flag vence (vamos ignorar o arquivo).
    if final_from_lb && have_final
        @warn "--final-from-lb informado junto com arquivo finalLowerLo; ignorando arquivo e usando LB em m_min para definir finalLowerLo."
        have_final = false
        empty!(finalLowerLo)
    end

    m_cut = m_min
    blocks = Vector{Dict{String,Any}}()
    for x in 0:8
        uI = u_range_uniform(x; m_min=m_min, pbits=pbits)
        ωI = omega_I(uI)
        ent = Dict(
            "x" => x,
            "u_range" => interval_to_dict(uI),
            "omega_range" => interval_to_dict(ωI),
            "m_cut" => string(m_cut)
        )

        if final_from_lb
            # (A) Define finalLowerLo[x] := prevfloat(inf(LB_simp(m_min, x))) e marca ok=true
            LB_I = LB_interval_at(m_min, x; pbits=pbits)
            lb_lo = inf(LB_I)
            flx   = prevfloat(lb_lo)
            ent["finalLowerLo_q"]         = to_dec(flx)
            ent["LB_at_m_min_interval"]   = interval_to_dict(LB_I)
            ent["lb_base_lower"]          = to_dec(lb_lo)
            ent["lb_base_ok"]             = true
        elseif have_final
            # (B) Checa arquivo
            LB_I = LB_interval_at(m_min, x; pbits=pbits)
            lb_lo = inf(LB_I)
            ent["finalLowerLo_q"]         = to_dec(finalLowerLo[x])
            ent["LB_at_m_min_interval"]   = interval_to_dict(LB_I)
            ent["lb_base_lower"]          = to_dec(lb_lo)
            ent["lb_base_ok"]             = (lb_lo >= finalLowerLo[x])
        else
            ent["lb_base_ok"] = "omitted"
        end

        push!(blocks, ent)
    end

    payload = Dict(
        "type" => "uniform_LB_certificate",
        "pbits" => pbits,
        "C1" => to_dec(C1),
        "C2" => to_dec(C2),
        "domain" => domain,
        "by_x" => blocks,
        "notes" => "Uniform LB certificate for m ≥ $(m_min) and x=0..8. Base check at m_min uses interval arithmetic; monotonicity for m ≥ m_cut is intended to be proved in Lean."
    )

    open(outpath, "w") do io
        print(io, JSON.json(payload))
    end
    println("Wrote uniform LB certificate to: ", outpath)
    if final_from_lb
        println("Included finalLowerLo from LB_simp(m_min, x); lb_base_ok=true by construction.")
    elseif have_final
        println("Included base checks against provided finalLowerLo (and wrote lb_base_lower).")
    else
        println("No finalLowerLo file provided: wrote domain + placeholders (lb_base_ok=\"omitted\").")
    end
end

# -------------------------- CLI -------------------------------

if abspath(PROGRAM_FILE) == @__FILE__
    if length(ARGS) < 1 || length(ARGS) > 4
        println("""
        Usage:
          julia --project=external/julia external/julia/uniform_bridge_LB_18794.jl OUT.json [rows18794_finalLowerLo.json] [--pbits=256] [--final-from-lb]

        Examples:
          # Opção A (gera finalLowerLo via LB em m_min):
          julia --project=external/julia external/julia/uniform_bridge_LB_18794.jl Certs/uniform-LB-18794.json --pbits=256 --final-from-lb

          # Opção B (valida contra arquivo existente):
          julia --project=external/julia external/julia/uniform_bridge_LB_18794.jl Certs/uniform-LB-18794.json Certs/rows18794_finalLowerLo.json --pbits=256
        """)
        exit(1)
    end

    out = ARGS[1]
    local flos::Union{Nothing,String} = nothing
    local pbits = 256
    local final_from_lb = false

    for a in ARGS[2:end]
        if startswith(a, "--pbits=")
            pbits = parse(Int, split(a, "=")[2])
        elseif a == "--final-from-lb"
            final_from_lb = true
        else
            flos = a
        end
    end

    main(out; pbits=pbits, final_lo_file=flos, m_min=18794, final_from_lb=final_from_lb)
end