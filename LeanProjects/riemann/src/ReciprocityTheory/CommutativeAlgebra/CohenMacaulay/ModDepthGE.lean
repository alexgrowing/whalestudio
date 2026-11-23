import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim

namespace ReciprocityTheory.CA

variable (R : Type*) [CommRing R] [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M]

def ModDepthGE (n : ℕ) : Prop :=
  ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
    RingTheory.Sequence.IsRegular M rs

def IsCMMod : Prop :=
  IsNoetherianRing R ∧ Module.Finite R M ∧
    ∃ n : ℕ, Module.supportDim R M = n ∧ ModDepthGE R M n

end ReciprocityTheory.CA
