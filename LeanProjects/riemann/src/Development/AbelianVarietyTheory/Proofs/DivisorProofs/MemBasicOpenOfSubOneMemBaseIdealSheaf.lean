import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupport
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem mem_basicOpen_of_sub_one_mem_baseIdeal (R : Type) [CommRing R] (I : Ideal R) (Z : Scheme.{0})
    (p : Z ⟶ Spec (CommRingCat.of R)) (V : Z.Opens) (hV : IsAffineOpen V) (r : Γ(Z, V)) (z : Z)
    (hz : z ∈ V) (hI : I ≤ (p z).asIdeal) (hr : r - 1 ∈ (baseIdeal p I).ideal ⟨V, hV⟩) :
    z ∈ Z.basicOpen r := by
  have hs : z ∈ (baseIdeal p I).support := (mem_support_baseIdeal p I z).2 hI
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hz] at hs
  have h1 : z ∉ Z.basicOpen (r - 1) := by
    rw [Scheme.mem_zeroLocus_iff] at hs
    exact hs _ hr
  rw [Scheme.mem_basicOpen _ _ _ hz] at h1 ⊢
  have hsum : Z.presheaf.germ V z hz r + (-(Z.presheaf.germ V z hz (r - 1))) = 1 := by
    simp [map_sub]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with h | h
  · exact h
  · exact absurd (by simpa using h.neg) h1

end GlobalTheory.FormalAlg
