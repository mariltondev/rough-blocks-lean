# bridge_certificate_18794.jl
using IntervalArithmetic
import IntervalArithmetic: interval
using JSON

# julia --project=external/julia external/julia/bridge_certificate_18794.jl certs/uniform-bridge-ge-18794.json

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

# Constrói, para cada x, um "u-range" UNIFORME em m∈[18794,∞):
# O máximo de u(m,x) ocorre no m mínimo.
function u_range_uniform(x::Int; m_min::BigFloat, pbits::Int)
    setprecision(BigFloat, pbits)
    X  = m_min*m_min + BigFloat(x)*m_min
    u_at_m_min = log(interval(X, X)) / log(interval(m_min, m_min))
    u_hi = sup(u_at_m_min)
    u_lo = big(2) # Limite inferior quando m→∞
    return interval(u_lo, u_hi)
end

# Helper pra serializar Interval{BigFloat} como strings decimais
to_dec(o) = string(o)
function interval_to_dict(I::Interval{BigFloat})
    return Dict("lo" => to_dec(inf(I)), "hi" => to_dec(sup(I)))
end

function main(outpath::String; m_min_val::Int, pbits::Int)
    setprecision(BigFloat, pbits)
    m_min_bf = BigFloat(m_min_val)

    logm_min  = log(interval(m_min_bf, m_min_bf))
    domain    = Dict{String,Any}()
    domain["m_min"]   = string(m_min_val)
    domain["x_range"] = Dict("lo"=>"0","hi"=>"8")
    domain["logm_min_interval"] = interval_to_dict(logm_min)

    blocks = Vector{Dict{String,Any}}()
    for x in 0:8
        uI   = u_range_uniform(x; m_min=m_min_bf, pbits=pbits)
        ωI   = omega_I(uI)
        push!(blocks, Dict(
            "x" => x,
            "u_range_certified" => interval_to_dict(uI),
            "omega_range_certified" => interval_to_dict(ωI)
        ))
    end

    @assert all(block["u_range_certified"]["lo"] == "2.0" for block in blocks)

    payload = Dict(
        "type" => "uniform_bridge_domain_certificate",
        "pbits" => pbits,
        "domain" => domain,
        "by_x" => blocks,
        "notes" => "This JSON certifies the parameter regime uniformly for all m >= $(m_min_val) and x in 0..8."
    )

    open(outpath, "w") do io
        print(io, JSON.json(payload, 2)) # Usando indentação para legibilidade
    end

    println("Wrote uniform certificate for m >= $(m_min_val) to: ", outpath)
end

# Ponto de entrada
if abspath(PROGRAM_FILE) == @__FILE__
    main("certs/uniform-bridge-ge-18794.json"; m_min_val=18794, pbits=256)
end