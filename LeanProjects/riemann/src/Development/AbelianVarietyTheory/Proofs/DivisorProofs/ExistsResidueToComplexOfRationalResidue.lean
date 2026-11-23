import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem exists_residue_complex : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K) (h : IsLocModel (algebraMap ℂ K) R),
  RatRes (algebraMap ℂ K) R →
  ∃ ε : R →+* ℂ, (∀ a : ℂ, ε ⟨algebraMap ℂ K a, h.const_mem a⟩ = a) ∧ ∀ r : R, ε r = 0 ↔ NonUnit R (r : K) := by
  intro K _ _ R h hr
  haveI := h.isLocalRing
  let c0 : ℂ →+* R := (algebraMap ℂ K).codRestrict R h.const_mem
  let φ : ℂ →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp c0
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun y => ?_⟩
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := hr r r.2
    refine ⟨a, ?_⟩
    have hn : NonUnit R ((r - c0 a : R) : K) := by simpa [c0] using ha
    have hm : r - c0 a ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal _).2 ((nonUnit_iff (R := R) (r - c0 a)).1 hn)
    have := (IsLocalRing.residue_eq_zero_iff (r - c0 a)).2 hm
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  let e := RingEquiv.ofBijective φ hφ
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue R), fun a => ?_, fun r => ?_⟩
  · show e.symm (φ a) = a
    exact e.symm_apply_apply a
  · rw [nonUnit_iff (R := R) r, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_eq_zero_iff _ e.symm.injective, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]

end GlobalTheory.FieldPair
