import Formalism.SizeWindowBrackets.JointCSlopeExists
import Formalism.SizeWindowBrackets.ChainSlopeWindows.IntersectionFailsForSubmodule
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainLatticeSizesModelEventually

open Module NumberField
open scoped Pointwise

noncomputable section

namespace Formalism.LFunctionChainParameters.LJC

open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData Formalism.LFunctionChainParameters.DiagonalSublatticeLength

section Str

variable {K : Type} [Field K] [NumberField K]

end Str

section Glob

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

end Glob

section Loc

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

end Loc

section Joint

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

end Joint

section Smith

variable {R : Type} [CommRing R] [IsDomain R]
variable {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
variable {W : Type} [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]

end Smith

section Smith2

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

end Smith2

section Slope

end Slope

section Local

end Local

section Fam

variable {K V V₂ : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V₂] [Module K V₂] [Module (𝓞 K) V₂]
  [IsScalarTower (𝓞 K) K V₂]

end Fam

section More

theorem exists_unif {K : Type} [Field K] [NumberField K] (w : FinPl K) :
    ∃ x : 𝓞 K, x ∈ w.1 ∧ x ∉ w.1 ^ 2 := by
  obtain ⟨x, hx, hx'⟩ := Ideal.exists_mem_pow_notMem_pow_succ w.1 (finPl_ne_bot w) w.2.ne_top 1
  exact ⟨x, by simpa using hx, hx'⟩

end More

section Prim

end Prim

section Real

variable {ι κ : Type*} [DecidableEq ι]

end Real

section Tests

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

end Tests

end Formalism.LFunctionChainParameters.LJC
