# generate_lean_uniform_bridge_increment_18794.jl
# Converte certs/uniform-bridge-increment-18794.json em um arquivo Lean com margens em ℚ.
# julia --project=. external/julia/generate_lean_uniform_bridge_increment_18794.jl

using JSON

function dec_to_rat_lean(s::String)
    # Caso 1: forma "num//den" já racionalizada
    if occursin("//", s)
        parts = split(s, "//")
        if length(parts) != 2
            error("Rational format not recognized: " * s)
        end
        num = strip(parts[1])
        den = strip(parts[2])
        return "((" * num * " : ℚ) / (" * den * " : ℚ))"
    end
    # Caso 2: decimal finito
    if occursin("e", lowercase(s))
        error("Formato científico não suportado: $s")
    end
    if !occursin(".", s)
        return "(" * s * " : ℚ)"
    end
    parts = split(s, ".")
    intp = parts[1]
    frac = parts[2]
    sign = startswith(s, "-") ? "-" : ""
    if sign != ""
        intp = replace(intp, "-"=>"")
    end
    # se fração é toda zero, devolve inteiro
    if all(c -> c == '0', frac)
        return "(" * sign * intp * " : ℚ)"
    end
    num = intp * frac
    # remover zeros à esquerda
    num = replace(num, r"^0+" => "")
    if isempty(num)
        return "(0 : ℚ)"
    end
    pow = string(length(frac))
    num_expr = sign * num
    return "((" * num_expr * " : ℚ) / (10^" * pow * " : ℚ))"
end

function main(json_in::String, lean_out::String)
    cert = JSON.parsefile(json_in)
    byx = cert["by_x"]
    open(lean_out, "w") do io
        # Cabeçalho opcional removido para evitar erros de parser no Lean.
        println(io, "import Mathlib\n")
        println(io, "namespace RoughBlocks.External.Certs\n")
        println(io, "structure BridgeRow where\n  x : ℕ\n  uLo : ℚ\n  uHi : ℚ\n  omegaLo : ℚ\n  omegaHi : ℚ\n  tMainLo : ℚ\n  m2Lo : ℚ\n  rLo : ℚ\n  e1Up : ℚ\n  e2 : ℚ\n  finalLowerLo : ℚ\n  lbHi : ℚ\n  deltaLo : ℚ\n")
        println(io, "def rows18794 : List BridgeRow := [")
        for (i,blk) in enumerate(byx)
            x = blk["x"]
            u = blk["u_interval_q"]
            w = blk["omega_interval_q"]
            uLo = dec_to_rat_lean(u["lo"]) ; uHi = dec_to_rat_lean(u["hi"]) 
            wLo = dec_to_rat_lean(w["lo"]) ; wHi = dec_to_rat_lean(w["hi"]) 
            tMainLo = dec_to_rat_lean(blk["t_main_lo_q"]) 
            m2Lo    = dec_to_rat_lean(blk["m2_lo_q"]) 
            rLo     = dec_to_rat_lean(blk["r_lo_q"]) 
            e1Up    = dec_to_rat_lean(blk["e1_up_q"]) 
            e2      = dec_to_rat_lean(blk["e2_q"]) 
            finalLo = dec_to_rat_lean(blk["final_lower_lo_q"]) 
            lbHi    = dec_to_rat_lean(blk["lb_hi_q"]) 
            dLo     = dec_to_rat_lean(blk["delta_lo_q"]) 
            print(io, "  { x := ", x, ", uLo := ", uLo, ", uHi := ", uHi,
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
        println(io, "end RoughBlocks.External.Certs\n")
    end
    println("Wrote Lean margins to: ", lean_out)
end

if abspath(PROGRAM_FILE) == @__FILE__
    json_in = get(ENV, "CERT_JSON", "certs/uniform-bridge-increment-18794.json")
    lean_out = get(ENV, "LEAN_OUT", "RoughBlocks/External/Certs/UniformGE18794Bridge.lean")
    main(json_in, lean_out)
end
