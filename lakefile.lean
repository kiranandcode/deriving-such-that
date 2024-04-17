import Lake
open Lake DSL

package derive_such_that where
  leanOptions := #[
   ⟨`pp.unicode.fun, true⟩, -- pretty prints `fun a ↦ b`
   ⟨`pp.proofs.withType, false⟩
  ]

@[default_target]
lean_lib DerivingSuchThat where
  -- add library configuration here


@[default_target]
lean_lib Tests {
  globs := #[.submodules "Tests"]
  leanOptions := #[⟨`linter.unusedVariables, false⟩]
}
