import Lake
open Lake DSL

package cmu_itp_24 where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib CmuItp24
