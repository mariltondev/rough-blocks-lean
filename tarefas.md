perfeito — vamos cravar o plano da Opção 2 (3 tarefas), usando o corte em 18 794:
	•	faixa finita: 2 \le m \le 18\,793 → técnica 1 (certificado JSON verificável em Lean, sem axioma);
	•	ponte analítica: m \ge 18\,794 → nova ponte uniforme (mesma ideia da atual, só que começando em 18 794);
	•	colar tudo no Light/ e limpar o Spec de axiomas desnecessários.

abaixo vai o roteiro cirúrgico, com nomes de arquivos, esquemas e pontos de validação.

⸻

Tarefa 1 — Faixa finita 2 \le m \le 18\,793 via técnica 1 (JSON → verificado em Lean)

Objetivo: eliminar o axioma budget_verified_by_scan e substituí-lo por um teorema em Lean que lê um certificado JSON e verifica cada par (m,x).

1.1. Certificado (lado Julia)
	•	Arquivo de saída: certs/finite-witnesses-2-18793.json
	•	Conteúdo por (m,x): um testemunho n e a fatoração completa de n (pares (p,e)), garantindo que o menor primo da fatoração é > m.
Isso permite ao Lean verificar rapidamente:
	1.	n \in K_x,
	2.	n = \prod p^e,
	3.	Nat.Prime p para cada p,
	4.	p > m para todos os fatores ⇒ P^-(n) > m.

Esquema JSON (exemplo):

{
  "meta": {
    "range": {"m_min": 2, "m_max": 18793},
    "blocks": 9,
    "created_utc": "2025-10-19T00:00:00Z",
    "julia_version": "1.10.5",
    "generator": "scripts/generate_finite_cert.jl",
    "sha256": "TO-BE-FILLED-AFTER-WRITE"
  },
  "data": [
    {
      "m": 1000,
      "x": 3,
      "n": 1000*1000 + 3*1000 + 17,
      "factors": [[2003,1], [499,1]]   // exemplo ilustrativo
    }
    // ... um item para cada (m,x), x=0..8
  ]
}

Por que fatoração completa?
Verificar “P^-(n)>m” vira barato: basta checar primalidade de poucos p e p>m. Evita rodar um crivo grande dentro do Lean.

1.2. Verificador (lado Lean)
	•	Novo módulo: RoughBlocks/Light/FiniteCert.lean
	•	Passos internos:
	•	Parse do JSON (use Lean.Data.Json).
	•	Estrutura:

structure Witness where
  m : Nat
  x : Nat
  n : Nat
  factors : List (Nat × Nat)  -- (p,e)


	•	Checagens por item:
	•	0 ≤ x ∧ x ≤ 8
	•	n ∈ K_x (def já existe)
	•	n = ∏ p^e (fold no ℕ)
	•	∀ (p,e) ∈ factors, Nat.Prime p ∧ e > 0 ∧ m < p
	•	Lema útil:

lemma mRough_of_factorization
  (hprod : n = ∏ (p,e) in factors, p ^ e)
  (hall  : ∀ (p,e) ∈ factors, Nat.Prime p ∧ m < p ∧ 0 < e)
  : mRough m n := by
  -- prova: menor primo de n é > m


	•	Teorema agregado (sem axioma):

theorem budget_verified_by_cert_2_18793
  : ∀ m, 2 ≤ m ∧ m ≤ 18793 → ∀ x, x ≤ 8 → ∃ n, BlockHasMRough m x n := ...


	•	Fail-fast: verifique hash do JSON antes de parsear:
	•	Armazene expectedSha256 : String em FiniteCert.lean.
	•	Compute SHA256 do arquivo em Lean (ou compare um --#eval que imprime hash e faça teste na CI).

1.3. Aceite (checks)
	•	#print axioms não menciona mais nada relativo a 2\le m\le 18\,793.
	•	#eval de um selftest que valida alguns (m,x) aleatórios do JSON.
	•	CI roda lake build + teste que falha se o SHA não bater.

⸻

Tarefa 2 — Nova ponte uniforme a partir de 18 794 (ajuste do threshold)

Objetivo: trocar a ponte “ge_1e6” por “ge_18794”.

2.1. Certificado (lado Julia)
	•	Script já existente: external/julia/uniform_bridge_certificate.jl
	•	Rodar com: --mmin 18794 (mantendo demais parâmetros).
	•	Saída: certs/uniform-bridge-ge-18794.json
	•	Inclua meta (faixa, versão, precisão de intervalo, seeds = none).
	•	Inclua sha256 no final, depois de gravar o arquivo.

2.2. Fio Lean
	•	Novo (ou renomeado): RoughBlocks/External/BridgeUniform.lean
	•	Mantenha o mesmo shape atual, só mudando nomes:
	•	bridge_ge_1e6_uniform ⟶ bridge_ge_18794_uniform
	•	certs/uniform-bridge-ge-1e6.json ⟶ certs/uniform-bridge-ge-18794.json
	•	Se continuar como axioma (como hoje), o Spec mostrará apenas um axioma: a ponte ge_18794.
	•	(Opcional, mais forte) se quiser, guarde também o SHA e exija a presença do arquivo certo.

2.3. Numeric/Light
	•	Ajustes nominais:
	•	margin_ge_one_from_1e6 ⟶ margin_ge_one_from_18794
	•	Onde aparecer m\ge 10^6, trocar para m\ge 18\,794.
	•	Light/Export.lean: exponha main_theorem_ge_18794 (ou mantenha o nome antigo mas com docstring atualizada).
	•	Checagem de hipóteses: garanta que quaisquer lemas que usavam “m\ge 10^6” só precisavam do sinal da margem (e não do valor de m). Se algum passo dependia de “m grande” de forma explícita, certifique que o certificado cobre essa parte.

2.4. Aceite
	•	#print axioms lista apenas a ponte bridge_ge_18794_uniform.
	•	Prova pública exposta:
\forall m\ge 18\,794,\ \forall x\le 8,\ \mathrm{LB}(m,x)\ge 1.

⸻

Tarefa 3 — Plumbing final (Spec, Export, CI, docs e release)
	1.	Spec / auditoria

	•	RoughBlocks/Light/Spec.lean: agora deve mostrar:
	•	❌ removido: budget_verified_by_scan
	•	✅ resta: bridge_ge_18794_uniform (se mantido como axioma)
	•	Um #eval que imprime:
	•	caminho dos dois JSON,
	•	seus SHA256,
	•	contagem de entradas esperadas (9*(18793-1+1) = 9*18792 = 169 128 itens).

	2.	Export

	•	RoughBlocks/Light/Export.lean:
	•	exporte dois resultados:
	•	budget_main_finite : ∀ m∈[2,18793], ∀ x≤8, ...
	•	budget_main_asymptotic : ∀ m≥18794, ∀ x≤8, ...
	•	e o “faixa total” como corolário.

	3.	CI

	•	Job que:
	•	confere SHA dos dois JSON,
	•	compila Lean,
	•	roda um smoke #eval que amostra 10 entradas e verifica mRough.

	4.	Docs

	•	certs/README.md com:
	•	schema resumido,
	•	comandos para (re)gerar,
	•	sha256sum esperado,
	•	como rodar o self-check do Lean.

	5.	Release

	•	CHANGELOG.md: “v2.0.0 — corte reduzido para 18 794; faixa finita verificada em Lean; única dependência externa: ponte uniforme ge_18794”.
	•	Tag v2.0.0 quando os dois certificados + CI estiverem verdes.
	•	(Opcional) subir nova versão no Zenodo espelhando os dois JSON + SHAs.

⸻

O que já podemos fazer agora (na canary)
	1.	Criar esqueleto do verificador finito:
	•	RoughBlocks/Light/FiniteCert.lean (parser + tipos + TODOs).
	•	certs/README.md com o schema acima.
	2.	Trocar nomes da ponte (sem mudar lógica):
	•	duplicar BridgeUniform.lean para aceitar ge_18794 (com TODO do JSON).
	3.	Exportar as novas assinaturas em Light/Export.lean (com sorry provisório, até os certificados entrarem).

Se quiser, eu já te escrevo os stubs de Lean (parser + assinaturas/teoremas) para colar no projeto — é só dizer que eu mando os blocos de código.

julia --project=external/julia -e '
include("external/julia/generate_finite_cert.jl");
ws = generate_range(2, 1000; blocks=9);
mkpath("certs");
obj = to_json_obj(ws; mmin=2, mmax=1000, blocks=9);
sha = write_with_sha("certs/finite-witnesses-00002-01000.json", obj);
println("OK  certs/finite-witnesses-00002-01000.json");
println("SHA256_DATA = ", sha);
'
jq -r '.data | length' certs/finite-witnesses-00002-01000.json
jq -r '.meta.sha256_data' certs/finite-witnesses-00002-01000.json


julia --project=external/julia -e '
include("external/julia/generate_finite_cert.jl");
ws = generate_range(1001, 3000; blocks=9);
mkpath("certs");
obj = to_json_obj(ws; mmin=1001, mmax=3000, blocks=9);
sha = write_with_sha("certs/finite-witnesses-01001-03000.json", obj);
println("OK  certs/finite-witnesses-01001-03000.json");
println("SHA256_DATA = ", sha);
'
jq -r '.data | length' certs/finite-witnesses-01001-03000.json
jq -r '.meta.sha256_data' certs/finite-witnesses-01001-03000.json


julia --project=external/julia -e '
include("external/julia/generate_finite_cert.jl");
ws = generate_range(3001, 6000; blocks=9);
mkpath("certs");
obj = to_json_obj(ws; mmin=3001, mmax=6000, blocks=9);
sha = write_with_sha("certs/finite-witnesses-03001-06000.json", obj);
println("OK  certs/finite-witnesses-03001-06000.json");
println("SHA256_DATA = ", sha);
'
jq -r '.data | length' certs/finite-witnesses-03001-06000.json
jq -r '.meta.sha256_data' certs/finite-witnesses-03001-06000.json


julia --project=external/julia -e '
include("external/julia/generate_finite_cert.jl");
ws = generate_range(6001, 10000; blocks=9);
mkpath("certs");
obj = to_json_obj(ws; mmin=6001, mmax=10000, blocks=9);
sha = write_with_sha("certs/finite-witnesses-06001-10000.json", obj);
println("OK  certs/finite-witnesses-06001-10000.json");
println("SHA256_DATA = ", sha);
'
jq -r '.data | length' certs/finite-witnesses-06001-10000.json
jq -r '.meta.sha256_data' certs/finite-witnesses-06001-10000.json


julia --project=external/julia -e '
include("external/julia/generate_finite_cert.jl");
ws = generate_range(10001, 14000; blocks=9);
mkpath("certs");
obj = to_json_obj(ws; mmin=10001, mmax=14000, blocks=9);
sha = write_with_sha("certs/finite-witnesses-10001-14000.json", obj);
println("OK  certs/finite-witnesses-10001-14000.json");
println("SHA256_DATA = ", sha);
'
jq -r '.data | length' certs/finite-witnesses-10001-14000.json
jq -r '.meta.sha256_data' certs/finite-witnesses-10001-14000.json


julia --project=external/julia -e '
include("external/julia/generate_finite_cert.jl");
ws = generate_range(14001, 18793; blocks=9);
mkpath("certs");
obj = to_json_obj(ws; mmin=14001, mmax=18793, blocks=9);
sha = write_with_sha("certs/finite-witnesses-14001-18793.json", obj);
println("OK  certs/finite-witnesses-14001-18793.json");
println("SHA256_DATA = ", sha);
'
jq -r '.data | length' certs/finite-witnesses-14001-18793.json
jq -r '.meta.sha256_data' certs/finite-witnesses-14001-18793.json




-- Light/CertSmoke.lean
import RoughBlocks.Light.FiniteCert

open RoughBlocks.Light

def summarize (path : System.FilePath) : IO Unit := do
  let arr ← verifyPart path
  let total : Nat := arr.size
  let oks   : Nat := (arr.filter (fun ⟨_, b⟩ => b)).size
  let fails : Nat := total - oks
  IO.println s!"File: {path}"
  IO.println s!"Total: {total}, OK: {oks}, FAIL: {fails}"
  if fails ≠ 0 then
    for ⟨w, b⟩ in arr do
      if !b then
        IO.println s!"FAIL m={w.m} x={w.x} n={w.n} factors={repr w.factors}"


-- #eval summarize ⟨"certs/finite-witnesses-00002-00020.json"⟩
-- #eval summarize ⟨"certs/finite-witnesses-00002-01000.json"⟩
-- #eval summarize ⟨"certs/finite-witnesses-01001-03000.json"⟩
-- #eval summarize ⟨"certs/finite-witnesses-03001-06000.json"⟩
-- #eval summarize ⟨"certs/finite-witnesses-06001-10000.json"⟩
-- #eval summarize ⟨"certs/finite-witnesses-10001-14000.json"⟩
-- #eval summarize ⟨"certs/finite-witnesses-14001-18793.json"⟩




julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-00002-01000.json
julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-01001-03000.json
julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-03001-06000.json
julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-06001-10000.json
julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-10001-14000.json
julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-14001-18793.json


xx

caffeinate -dimsu env LAKE_JOBS=8 lake -v build RoughBlocks.Light.Native.Compute18793 
caffeinate -dimsu env LAKE_JOBS=1 time lake -v build RoughBlocks.Light.Native.Compute18793
caffeinate -dimsu env LAKE_JOBS=1 time lake build RoughBlocks.Light.Native.Compute18793



caffeinate -dimsu env LAKE_JOBS=8 lake -v build RoughBlocks.Light.FiniteBridge_18793
lake -v build RoughBlocks.Light.FiniteBridge_18793

caffeinate -dimsu env LAKE_JOBS=8 lake -v build RoughBlocks.Light.Generated.FiniteData_00002_01000
lake -v build RoughBlocks.Light.Generated.FiniteData_00002_01000
lake build RoughBlocks.Light.Generated.FiniteData_00002_00100
 

docker run --rm -it -v "$PWD":/workdir -w /workdir roughblocks-build \
  bash -lc 'ulimit -s unlimited || true; lake build RoughBlocks.Light.Generated.FiniteData_00002_01000'


docker run --rm -it -v "$PWD":/workdir -w /workdir roughblocks-build \
  bash -lc 'ulimit -s unlimited || true; lake -v build RoughBlocks.Light.Generated.FiniteData_00002_01000 2>&1 | sed -n "1,120p"'


bash -lc 'docker run --rm -t --ulimit stack=262144:262144 -v "$PWD":/work -w /work rb-lean bash -lc '"'"'/usr/local/julia/bin/julia --project=external/julia -e "using Pkg; Pkg.instantiate(); Pkg.precompile()" && /usr/local/julia/bin/julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-01001-03000.json && lake build RoughBlocks.Light.Generated.FiniteData_01001_03000'"'"


bash -lc 'docker run --rm -t \
  --ulimit stack=67108864:67108864 \
  -v "$PWD":/work -w /work rb-lean \
  bash -lc "/usr/local/julia/bin/julia --project=external/julia -e \"using Pkg; Pkg.instantiate(); Pkg.precompile()\" && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/filter_cert.jl certs/finite-witnesses-00002-01000.json certs/finite-witnesses-00002-00500.json 2 500 && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-00002-00500.json && \
             lake build -j 2 RoughBlocks.Light.Generated.FiniteData_00002_00500 2>&1 | tee build_00002_00500.log"'

bash -lc 'docker run --rm -t \
  --ulimit stack=67108864:67108864 \
  -v "$PWD":/work -w /work rb-lean \
  bash -lc "/usr/local/julia/bin/julia --project=external/julia -e \"using Pkg; Pkg.instantiate(); Pkg.precompile()\" && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/filter_cert.jl certs/finite-witnesses-00002-01000.json certs/finite-witnesses-00002-00500.json 2 500 && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-00002-00500.json && \
             lake -K:jobs=2 build RoughBlocks.Light.Generated.FiniteData_00002_00500 2>&1 | tee build_00002_00500.log"'
 

bash -lc 'docker run --rm -t \
  --ulimit stack=536870912:536870912 \
  -v "$PWD":/work -w /work rb-lean \
  bash -lc "/usr/local/julia/bin/julia --project=external/julia -e \"using Pkg; Pkg.instantiate(); Pkg.precompile()\" && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/filter_cert.jl certs/finite-witnesses-00002-01000.json certs/finite-witnesses-00002-00500.json 2 500 && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-00002-00500.json && \
             lake -K:jobs=2 build RoughBlocks.Light.Generated.FiniteData_00002_00500 2>&1 | tee build_00002_00500.log"'



bash -lc 'docker run --rm -t \
  --ulimit stack=1073741824:1073741824 \
  -v "$PWD":/work -w /work rb-lean \
  bash -lc "/usr/local/julia/bin/julia --project=external/julia -e \"using Pkg; Pkg.instantiate(); Pkg.precompile()\" && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/filter_cert.jl certs/finite-witnesses-00002-01000.json certs/finite-witnesses-00002-00500.json 2 500 && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-00002-00500.json && \
             lake -K:jobs=2 build RoughBlocks.Light.Generated.FiniteData_00002_00500 2>&1 | tee build_00002_00500.log"'



bash -lc 'docker run --rm -t \
  --ulimit stack=1073741824:1073741824 \
  -v "$PWD":/work -w /work rb-lean \
  bash -lc "/usr/local/julia/bin/julia --project=external/julia -e \"using Pkg; Pkg.instantiate(); Pkg.precompile()\" && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/filter_cert.jl certs/finite-witnesses-00002-01000.json certs/finite-witnesses-00002-00100.json 2 100 && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-00002-00100.json && \
             lake -K:jobs=2 build RoughBlocks.Light.Generated.FiniteData_00002_00100 2>&1 | tee build_00002_00100.log"'





bash -lc 'docker run --rm -t \
  --ulimit stack=1073741824:1073741824 \
  -v "$PWD":/work -w /work rb-lean \
  bash -lc "/usr/local/julia/bin/julia --project=external/julia -e \"using Pkg; Pkg.instantiate(); Pkg.precompile()\" && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/filter_cert.jl certs/finite-witnesses-00002-01000.json certs/finite-witnesses-00002-00100.json 2 100 && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-00002-00100.json && \
             lake -K:jobs=2 build RoughBlocks.Light.Generated.FiniteData_00002_00100 2>&1 | tee build_00002_00100.log"'

 



 bash -lc 'docker run --rm -t \
  --ulimit stack=1073741824:1073741824 \
  -v "$PWD":/work -w /work rb-lean \
  bash -lc "/usr/local/julia/bin/julia --project=external/julia -e \"using Pkg; Pkg.instantiate(); Pkg.precompile()\" && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/filter_cert.jl certs/finite-witnesses-00002-01000.json certs/finite-witnesses-00021-00040.json 21 40 && \
             /usr/local/julia/bin/julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-00021-00040.json && \
             LAKE_JOBS=1 lake build RoughBlocks.Light.Generated.FiniteData_00021_00040 2>&1 | tee build_00021_00040.log"'



bash -lc 'docker run --rm -t \
  --ulimit stack=1073741824:1073741824 \
  -e NO_AGG=1 \
  -v "$PWD":/work -w /work rb-lean \
  bash -lc "/usr/local/julia/bin/julia --project=external/julia -e \"using Pkg; Pkg.instantiate(); Pkg.precompile()\" && \
            /usr/local/julia/bin/julia --project=external/julia external/julia/filter_cert.jl certs/finite-witnesses-00002-01000.json certs/finite-witnesses-00041-00060.json 41 60 && \
            /usr/local/julia/bin/julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-00041-00060.json && \
            lake -K:jobs=1 build RoughBlocks.Light.Generated.FiniteData_00041_00060 2>&1 | tee build_00041_00060_noagg.log"'



bash -lc 'docker run --rm -t \
  --ulimit stack=1073741824:1073741824 \
  -e NO_AGG=1 -e NO_ALLX=1 \
  -v "$PWD":/work -w /work rb-lean \
  bash -lc "/usr/local/julia/bin/julia --project=external/julia -e \"using Pkg; Pkg.instantiate(); Pkg.precompile()\" && \
            /usr/local/julia/bin/julia --project=external/julia external/julia/codegen_finite_lean.jl certs/finite-witnesses-00041-00060.json RoughBlocks/Light/Generated 1 && \
            for m in \$(seq 41 60); do \
              mod=RoughBlocks.Light.Generated.FiniteData_\$(printf %05d \$m)_\$(printf %05d \$m); \
              echo === Building \$mod ===; \
              LAKE_JOBS=1 lake -K:leanArgs=\"-DmaxRecDepth=200 -DmaxHeartbeats=400000\" build \$mod || { echo FAILED m=\$m; exit 1; }; \
            done"'

			




(base) mariltoncr@MacBook-Pro-de-Marilton rough-blocks-lean % julia --project=external/julia external/julia/bridge_increment_18793.jl

(base) mariltoncr@MacBook-Pro-de-Marilton rough-blocks-lean % jq . certs/uniform-bridge-increment-18793.json | head

(base) mariltoncr@MacBook-Pro-de-Marilton rough-blocks-lean % jq -r '.by_x[] | [.x, .delta_lo_q] | @tsv' certs/uniform-bridge-increment-18793.json



RECOMENDACAO AO PAPER PARA O CERTIFICADO JULIA DA PONTE

\begin{remark}[Parâmetro de \(\Phi\) na ponte]
No desenvolvimento analítico desta seção trabalhamos com o parâmetro \(y:=m\) na função \(\Phi\) (caso estrito, \(P^-(n)>m\)).
Na camada formal em Lean, a janela bloco\(\leftrightarrow\)\(\Phi\) aparece naturalmente com o caso não-estrito em \(m{+}1\), isto é, \(\Phi_{\mathrm{GE}}(\cdot,m{+}1)\).
Para \(n\ge 1\) vale a equivalência
\[
\Phi_{\mathrm{GT}}(x,m)=\Phi_{\mathrm{GE}}(x,m{+}1),
\]
de modo que não há lacuna entre as duas apresentações. Usaremos a desigualdade inferior
\[
LB(m,x)\;=\;\frac{m}{\log m}\,\omega\!\Big(\frac{\log(m^2+xm)}{\log m}\Big)\;-\;C_1\frac{m}{\log^2 m}\;-\;C_2
\]
com \(C_1\le 4.4\), \(C_2=100\), e a convenção \(\omega(u)=0\) para \(0<u<1\).
\end{remark}




