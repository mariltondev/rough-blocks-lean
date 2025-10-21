# Changelog
Todas as mudanças notáveis deste projeto serão documentadas aqui.

## [2.0.0-canary.1] – 2025-10-19
### Added
- Base para Opção 2: Técnica 1 (certificados JSON) para `2 ≤ m ≤ 18 793`.
- Preparação para refatorar a “ponte” (módulo ≥ 18 793) e ajustes no Light layer.

### Infra
- Criação da branch `canary`.
- Placeholder para certificados (`certs/.keep`).

## [1.0.0] – 2025-10-18
### Added
- Primeira release pública: prova Lean para `m ≥ 10^6`; varredura determinística como axioma para `2 ≤ m < 10^6`; certificado uniforme em Julia.