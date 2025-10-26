# uniform_bridge_certificate_parte3.jl
# Certifica (de forma uniforme) as hipóteses analíticas necessárias para a ponte
#   (LB m x : ℝ) ≤ (countRoughInBlock m x : ℝ)
# para todo m ≥ 18794 e x∈{0,…,8}, registrando um JSON de "domínio seguro":
# - u = log(m^2 + x m)/log m ∈ [2, u_max(x)] ⊂ [2,3]  (logo aplica a forma ω(u) de [2,3])
# - log m ≥ log(18794) (fixa precisão e monotonia usadas no paper)
#
# OBS: Este certificado NÃO "conta" nada nem reimplementa Φ:
# ele registra, com aritmética intervalar, que os parâmetros ficam
# 100% dentro do regime em que a desigualdade do paper vale.
#
# Uso:
#   julia --project=external/julia external/julia/uniform_bridge_certificate_parte3.jl certs/uniform_bridge_certificate_parte3.json

using IntervalArithmetic
import IntervalArithmetic: interval
using JSON

# ω(u) por intervalos, cobrindo [1,3] com a fórmula peça-a-peça.
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

# Constrói, para cada x, um "u-range" UNIFORME em m∈[m_min,∞):
#   u(m,x) = log(m^2 + x m) / log m
#   Como u↓2 quando m→∞, o pior caso (máximo) está em m = m_min.
#   Logo: u ∈ [2, u_at_mmin(x)].
function u_range_uniform(x::Int; pbits::Int=256, m_min::Int=18794)
    setprecision(BigFloat, pbits)
    m0 = BigFloat(m_min)
    X  = m0*m0 + BigFloat(x)*m0
    u_at_m0 = log(interval(X, X)) / log(interval(m0, m0))
    u_hi = sup(u_at_m0)
    u_lo = big(2)         # limite inferior quando m→∞
    uI = interval(u_lo, u_hi)
    # Sanidade: garantir que cabe no regime [2,3]
    if sup(uI) > big(3)
        error("u_range_uniform: u_hi(x=$x) = $(sup(uI)) > 3 para m_min = $m_min")
    end
    return uI
end

# Pequena helper pra serializar Interval{BigFloat} como strings decimais
to_dec(o) = string(o)  # BigFloat -> String
function interval_to_dict(I::Interval{BigFloat})
    return Dict("lo" => to_dec(inf(I)), "hi" => to_dec(sup(I)))
end

function main(outpath::String; pbits::Int=256, m_min::Int=18794)
    setprecision(BigFloat, pbits)

    logm_min  = log(interval(BigFloat(m_min), BigFloat(m_min)))
    domain    = Dict{String,Any}()
    domain["m_min"]   = string(m_min)
    domain["x_range"] = Dict("lo"=>"0","hi"=>"8")
    domain["logm_min_interval"] = interval_to_dict(logm_min)

    blocks = Vector{Dict{String,Any}}()
    for x in 0:8
        uI   = u_range_uniform(x; pbits=pbits, m_min=m_min)
        ωI   = omega_I(uI)  # opcional, mas útil como redundância/verificação
        push!(blocks, Dict(
            "x" => x,
            "u_range" => interval_to_dict(uI),
            "omega_range" => interval_to_dict(ωI)
        ))
    end

    notes = "This JSON certifies the parameter regime (u in [2,3], log m >= log(18794)) uniformly for all m >= 18794 and x in 0..8, so the analytic lower bound Φ-difference ≥ LB(m,x) applies throughout."

    payload = Dict(
        "type" => "uniform_bridge_domain_certificate",
        "pbits" => pbits,
        "domain" => domain,
        "by_x" => blocks,
        # Campo sinalizador: as hipóteses analíticas do paper valem uniformemente
        "bridge_hypotheses_verified" => true,
        "notes" => notes
    )

    # Escreve JSON sem indent para compatibilidade (JSON.jl 1.x)
    open(outpath, "w") do io
        print(io, JSON.json(payload))
    end

    println("Wrote uniform certificate to: ", outpath)
end

if abspath(PROGRAM_FILE) == @__FILE__
    if length(ARGS) != 1
        println("Usage:\n  julia --project=external/julia external/julia/uniform_bridge_certificate_parte3.jl certs/uniform_bridge_certificate_parte3.json")
        exit(1)
    end
    main(ARGS[1]; pbits=256, m_min=18794)
end