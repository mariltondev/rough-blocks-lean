# Contribuindo

Obrigado pelo interesse no RoughBlocks!

## Licença das contribuições
Ao enviar um PR, você concorda em licenciar sua contribuição sob a **Apache-2.0** (código).
Documentação e paper permanecem sob **CC BY-NC-ND 4.0**, salvo indicação em contrário.

## DCO (Developer Certificate of Origin)
Assine seus commits com:
```
git commit -s -m "feat: sua mensagem"
```
Isso certifica que você tem direito de submeter o código sob a licença do projeto.

## Escopo e estabilidade de API
- A superfície pública é a camada **Light** (`RoughBlocks.Light.*`).
- **Não** importe `RoughBlocks.Heavy.*` em projetos clientes.
- Veja `AUDIT.md` e `scripts/ci-local.sh` para auditoria local.

## Estilo
- Lean 4 + mathlib.
- Use nomes qualificados (`RoughBlocks.Light.*`).
- Adicione testes/hooks de especificação quando fizer sentido.

## Segurança / divulgações
Para relatos sensíveis, abra issue privada ou contate os mantenedores.
