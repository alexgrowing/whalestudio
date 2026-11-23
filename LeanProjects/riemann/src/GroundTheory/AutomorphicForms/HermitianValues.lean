import Mathlib
import GroundTheory.AutomorphicForms.HermitianBinaryValues
import GroundTheory.AutomorphicForms.HermitianLocalForms

noncomputable section

namespace GroundTheory.Automorphic

open NumberField IsDedekindDomain GroundTheory.Global NumberField.InfinitePlace.Completion

def Rep {F : Type*} [Field F] (d : F) {n : ℕ} (a : Fin n → F) (c : F) : Prop :=
  ∃ s : Fin n → F, (∀ i, SqNorm d (s i)) ∧ ∑ i, a i * s i = c

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]

end Local

section Real

variable {K : Type*} [Field K] {w : InfinitePlace K}

end Real

section Global

universe u

variable {K : Type u} [Field K] [NumberField K]

end Global

end GroundTheory.Automorphic
