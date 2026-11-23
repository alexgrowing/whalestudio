import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBasicOpenOfSubOneMemBaseIdealSheaf
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_basicOpen_of_sub_one_mem_baseIdealSheaf : ∀ (R : Type) [CommRing R] (I : Ideal R) (Z : Scheme.{0}) (p : Z ⟶ Spec (CommRingCat.of R)) (V : Z.Opens) (hV : IsAffineOpen V) (r : Γ(Z, V)) (z : Z), z ∈ V → I ≤ (p z).asIdeal → r - 1 ∈ (baseIdeal p I).ideal ⟨V, hV⟩ → z ∈ Z.basicOpen r := by
  first | exact @GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal | exact GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal | (intros; apply GlobalTheory.FormalAlg.mem_basicOpen_of_sub_one_mem_baseIdeal <;> assumption)
