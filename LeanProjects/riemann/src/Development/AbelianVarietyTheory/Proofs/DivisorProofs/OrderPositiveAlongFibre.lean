import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace GlobalTheory.SteinFibre

theorem ord_pos_of_mem_under (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (z : X)
    (t : Γ(X, ⊤)) (ht : t ∈ under z) (h0 : t ≠ 0) (hz : Order.coheight z = 1) :
    0 < Scheme.ord (algebraMap Γ(X, ⊤) X.functionField t) z := by
  set a := X.presheaf.germ ⊤ z trivial t with ha_def
  have ha : a ≠ 0 := fun h =>
    h0 (germ_injective_of_isIntegral X (U := ⊤) z trivial (h.trans (map_zero _).symm))
  have hna : ¬ IsUnit a := (mem_under_iff z t).1 ht
  have e : algebraMap Γ(X, ⊤) X.functionField t =
      algebraMap (X.presheaf.stalk z) X.functionField a := by
    letI : Algebra Γ(X, ⊤) (X.presheaf.stalk z) :=
      X.presheaf.algebra_section_stalk (⟨z, trivial⟩ : (⊤ : X.Opens))
    haveI := functionField_isScalarTower X ⊤ ⟨z, trivial⟩
    exact IsScalarTower.algebraMap_apply Γ(X, ⊤) (X.presheaf.stalk z) X.functionField t
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hnz := mem_nonZeroDivisors_of_ne_zero ha
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Ring.ord_ne_top hnz)
  have hord : Scheme.ord (algebraMap Γ(X, ⊤) X.functionField t) z = n := by
    rw [e]
    refine (Scheme.ord_eq_iff hz ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha)).2 ?_
    exact (Ring.ordFrac_eq_ord _ ha).trans (Ring.ordMonoidWithZeroHom_eq_coe _ hnz hn.symm)
  rw [hord]
  have : Nontrivial (X.presheaf.stalk z ⧸ Ideal.span {a}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rwa [ne_eq, Ideal.span_singleton_eq_top])
  have hpos : (0 : ℕ∞) < Ring.ord (X.presheaf.stalk z) a := by
    unfold Ring.ord
    exact Module.length_pos
  rw [← hn] at hpos
  have : 0 < n := by exact_mod_cast hpos
  exact_mod_cast this

end GlobalTheory.SteinFibre
