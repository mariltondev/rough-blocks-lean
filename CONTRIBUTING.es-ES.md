# Contribuir

¡Gracias por tu interés en RoughBlocks!

## Licencia de las contribuciones
Al enviar un PR, aceptas licenciar tu contribución bajo **Apache-2.0** (código).
La documentación y el paper permanecen bajo **CC BY-NC-ND 4.0**, salvo indicación en contrario.

## DCO (Developer Certificate of Origin)
Firma tus commits con:
```
git commit -s -m "feat: tu mensaje"
```
Esto certifica que tienes derecho a enviar el código bajo la licencia del proyecto.

## Alcance y estabilidad de la API
- La superficie pública es la capa **Light** (`RoughBlocks.Light.*`).
- **No** importes `RoughBlocks.Heavy.*` desde proyectos clientes.
- Consulta `AUDIT.md` y `scripts/ci-local.sh` para la auditoría local.

## Estilo
- Lean 4 + mathlib.
- Usa nombres calificados (`RoughBlocks.Light.*`).
- Añade tests/hooks de especificación cuando sea razonable.

## Seguridad / divulgaciones
Para reportes sensibles, abre un issue privado o contacta a los mantenedores.
