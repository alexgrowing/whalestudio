import Mathlib

open Matrix
open scoped ComplexOrder

namespace Bl.SecondBlockLemmaJ

theorem goal1 {K L ι n : Type} [Field K] [Field L] [Fintype ι] [Fintype n] [DecidableEq ι]
    [DecidableEq n] (τ : K →+* L) (c : ι → n → K) (hc : LinearIndependent K c) :
    LinearIndependent L (fun a => fun i => τ (c a i)) := by
  let : Algebra K L := τ.toAlgebra
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 τ.injective
  exact (linearIndependent_algebraMap_comp_iff (R := K) (S := L) (v := c)).2 hc

end Bl.SecondBlockLemmaJ
