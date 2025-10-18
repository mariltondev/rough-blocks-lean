# Contributing

Thanks for your interest in RoughBlocks!

## License of contributions
By submitting a pull request, you agree to license your contribution under the
**Apache License, Version 2.0** (for code). Documentation and the paper remain under
**CC BY-NC-ND 4.0** unless otherwise stated.

## Developer Certificate of Origin (DCO)
Please add a Signed-off-by line to your commits:
```
git commit -s -m "feat: your message"
```
This certifies that you have the right to submit the code under the project license.

## Scope & API stability
- The public surface is the **Light** layer (`RoughBlocks.Light.*`).
- Please **do not** import `RoughBlocks.Heavy.*` from downstream clients.
- See `AUDIT.md` for local audit steps and `scripts/ci-local.sh` for automation.

## Code style
- Lean 4 + mathlib.
- Prefer qualified names (`RoughBlocks.Light.*`).
- Add tests/spec hooks when feasible (e.g., `Light/Spec.lean`).

## Security / disclosures
For sensitive reports, please open a private issue or contact the maintainers directly.
