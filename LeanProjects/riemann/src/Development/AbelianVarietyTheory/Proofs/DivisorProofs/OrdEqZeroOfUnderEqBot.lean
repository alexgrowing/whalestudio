import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.SteinFibre

noncomputable def under {X : Scheme.{0}} (z : X) : Ideal Γ(X, ⊤) :=
  Ideal.comap (X.presheaf.germ ⊤ z trivial).hom (IsLocalRing.maximalIdeal (X.presheaf.stalk z))

theorem mem_under_iff {X : Scheme.{0}} (z : X) (a : Γ(X, ⊤)) :
    a ∈ under z ↔ ¬ IsUnit (X.presheaf.germ ⊤ z trivial a) := by
  simp only [under, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

instance under_isPrime {X : Scheme.{0}} (z : X) : (under z).IsPrime :=
  Ideal.comap_isPrime _ _

theorem under_le_of_specializes {X : Scheme.{0}} {z x : X} (h : z ⤳ x) : under z ≤ under x := by
  intro a ha
  rw [mem_under_iff] at ha ⊢
  intro hu
  apply ha
  have e := X.presheaf.germ_stalkSpecializes (U := ⊤) trivial h
  rw [← e, CommRingCat.comp_apply]
  exact hu.map (X.presheaf.stalkSpecializes h).hom

theorem ord_eq_zero_of_under_eq_bot {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (z : X)
    (a : Γ(X, ⊤)) (hz : under z = ⊥) (ha : a ≠ 0) :
    Scheme.ord (algebraMap Γ(X, ⊤) X.functionField a) z = 0 := by
  have hu : IsUnit (X.presheaf.germ ⊤ z trivial a) := by
    by_contra h
    have : a ∈ under z := (mem_under_iff z a).2 h
    rw [hz] at this
    exact ha this
  have hzV : z ∈ X.basicOpen a := (X.mem_basicOpen a z trivial).2 hu
  haveI : Nonempty (X.basicOpen a) := ⟨⟨z, hzV⟩⟩
  have h1 := Scheme.ord_of_isUnit (U := X.basicOpen a) (f := X.presheaf.map (homOfLE le_top).op a)
    (X.toRingedSpace.isUnit_res_basicOpen a) hzV
  rw [← h1]
  congr 1
  exact (X.presheaf.germ_res_apply (homOfLE le_top) _ _ a).symm

end GlobalTheory.SteinFibre
