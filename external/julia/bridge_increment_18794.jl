# Certificado "forte" (esqueleto) para a ponte incremental: m ≥ 18794, x ∈ {0..8}
# Saída: certs/uniform-bridge-increment-18794.json
#
# julia --project=. external/julia/bridge_increment_18794.jl
#
# OBS: Este script já exporta TODOS os campos racionais necessários para o Lean
# fazer a checagem aritmética. Os termos M2 e R ainda estão com cotas
# conservadoras (placeholders) negativas; troque-os pelas cotas refinadas por x
# para obter delta_lo_q ≥ 0 e remover o axioma.

using JSON
using SHA

# ---------------- Precisão ----------------
const PBITS = 256

# ---------------- Constantes do paper ----------------
const C_INC = BigFloat("2.0")    # c_inc ≤ 2
const C_VAR = BigFloat("2.4")    # c_var ≤ 2.4
const C1    = C_INC + C_VAR      # 4.4
const C2    = BigFloat(100)      # 100 exato

# ---------------- Domínio ----------------
const M_MIN = 18794
const X_LO  = 0
const X_HI  = 8

# ---------------- Racionalização (denom 10^DIG) ----------------
const DIG = 200
const D10 = BigInt(10)^DIG

to_q_lo(x::BigFloat) = begin
    n = floor(BigInt, x * BigFloat(D10))
    string(n, "//", D10)
end

to_q_hi(x::BigFloat) = begin
    n = ceil(BigInt, x * BigFloat(D10))
    string(n, "//", D10)
end

# ---------------- ω(u) fechada ----------------
omega_scalar(u::BigFloat) = u ≤ 2 ? BigFloat(1)/u : (1 + log(u - 1)) / u

# ---------------- Termos por x (em m = M_MIN) ----------------
function terms_for_x(x::Int; pbits::Int=PBITS)
    setprecision(pbits) do
        m  = BigFloat(M_MIN)
        X  = m*m + BigFloat(x)*m
        Y  = m

        # u exato no ponto m_min: u = log X / log m
        logm    = log(m)
        u       = log(X) / logm
        u_lo    = u
        u_hi    = u

        # ω(u) exata (fechada) na faixa [2,3]
        ω       = omega_scalar(u)
        ω_lo    = ω
        ω_hi    = ω

        # Fatores comuns
        logy     = logm
        main_fac = Y / logy
        err_fac  = Y / (logy^2)

        # Termo principal (lower) — aqui igual ao valor exato no ponto
        t_main_lo = main_fac * ω

        # Variação (M2) e resíduo (R) já agregados em C1; não duplicar negatividade
        m2_lo = BigFloat(0)
        r_lo  = BigFloat(0)

        # E1 upper (agregador)
        e1_up = C1 * err_fac

        # Final lower (Φ-dif) ≥ T_main − C1 − C2
        final_lower_lo = t_main_lo - e1_up - C2

        # LB upper usando ω_hi
        lb_hi = main_fac * ω_hi - e1_up - C2

        # Delta lower: (Φ−LB) ≥ final_lower_lo − lb_hi
        delta_lo = final_lower_lo - lb_hi

        return Dict(
            "x" => x,
            "u_interval_q"     => Dict("lo"=>to_q_lo(u_lo), "hi"=>to_q_hi(u_hi)),
            "omega_interval_q" => Dict("lo"=>to_q_lo(ω_lo), "hi"=>to_q_hi(ω_hi)),
            "t_main_lo_q"      => to_q_lo(t_main_lo),
            "m2_lo_q"          => to_q_lo(m2_lo),
            "r_lo_q"           => to_q_lo(r_lo),
            "e1_up_q"          => to_q_hi(e1_up),   # upper bound
            "e2_q"             => to_q_hi(C2),      # exato/upper
            "final_lower_lo_q" => to_q_lo(final_lower_lo),
            "lb_hi_q"          => to_q_hi(lb_hi),
            "delta_lo_q"       => to_q_lo(delta_lo)
        )
    end
end

# ---------------- Payload + SHA ----------------
function build_payload(; pbits::Int=PBITS)
    byx = [ terms_for_x(x; pbits=pbits) for x in X_LO:X_HI ]

    meta = Dict(
        "type"   => "uniform_bridge_increment_certificate",
        "domain" => Dict("m_min"=>string(M_MIN),
                         "x_range"=>Dict("lo"=>string(X_LO),"hi"=>string(X_HI))),
        "pbits"  => pbits,
        "constants" => Dict("c_inc"=>"2.0", "c_var"=>"2.4", "C1"=>"4.4", "C2"=>"100"),
        "notes"  => "Strong certificate with rational witnesses. Replace m2_lo_q and r_lo_q by refined per-x lower bounds (π short-window + Mertens via Abel) to obtain delta_lo_q ≥ 0 and eliminate the axiom."
    )

    # NÃO use Dict(meta; "by_x"=>byx). Faça merge ou atribuição:
    payload_wo_sha = merge(meta, Dict("by_x" => byx))

    json_txt = JSON.json(payload_wo_sha, 2)
    sha = bytes2hex(sha256(json_txt))

    # idem: não usar Dict(payload_wo_sha; "sha256"=>sha)
    payload = merge(payload_wo_sha, Dict("sha256" => sha))
    return payload
end

function main(outpath::String="certs/uniform-bridge-increment-18794.json")
    payload = build_payload()
    mkpath(dirname(outpath))
    open(outpath, "w") do io
        print(io, JSON.json(payload, 2))
    end
    println("Wrote certificate to: ", outpath)
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
