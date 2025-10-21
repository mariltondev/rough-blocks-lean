# generate_lean_uniform_bridge_18793.jl
# Lê certs/uniform-bridge-ge-18793.json e emite um arquivo Lean
# com os números como racionais exatos (ℚ) para verificação formal.

using JSON

function dec_to_rat_lean(s::String)
    # Converte string decimal finita para expressão Lean de um racional exato.
    # Ex.: "2.0005" -> "((20005 : ℚ) / (10^4 : ℚ))"; "0.0" -> "(0 : ℚ)".
    if occursin("e", lowercase(s))
        error("Formato científico não suportado: $s")
    end
    if !occursin(".", s)
        return "(" * s * " : ℚ)"
    end
    parts = split(s, ".")
    intp = parts[1]
    frac = parts[2]
    # remover possíveis sinais
    sign = startswith(s, "-") ? "-" : ""
    if sign != ""
        intp = replace(intp, "-"=>"")
    end
    # se parte fracionária é toda zero, devolve inteiro puro
    if all(c -> c == '0', frac)
        return "(" * sign * intp * " : ℚ)"
    end
    num = intp * frac
    # remover zeros à esquerda no numerador (exceto se tudo zero)
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
        println(io, "structure CertBlock where\n  x : ℕ\n  uLo : ℚ\n  uHi : ℚ\n  omegaLo : ℚ\n  omegaHi : ℚ\n")
        println(io, "def certs18793 : List CertBlock := [")
        for (i,blk) in enumerate(byx)
            x = blk["x"]
            u = blk["u_range_certified"]
            w = blk["omega_range_certified"]
            uLo = dec_to_rat_lean(u["lo"])
            uHi = dec_to_rat_lean(u["hi"])
            wLo = dec_to_rat_lean(w["lo"])
            wHi = dec_to_rat_lean(w["hi"])
            print(io, "  { x := ", x, ", uLo := ", uLo, ", uHi := ", uHi,
                  ", omegaLo := ", wLo, ", omegaHi := ", wHi, " }")
            if i < length(byx)
                println(io, ",")
            else
                println(io)
            end
        end
        println(io, "]\n")
        println(io, "end RoughBlocks.External.Certs\n")
    end
    println("Wrote Lean certificate to: ", lean_out)
end

if abspath(PROGRAM_FILE) == @__FILE__
    json_in = get(ENV, "CERT_JSON", "certs/uniform-bridge-ge-18793.json")
    lean_out = get(ENV, "LEAN_OUT", "RoughBlocks/External/Certs/UniformGE18793.lean")
    main(json_in, lean_out)
end
