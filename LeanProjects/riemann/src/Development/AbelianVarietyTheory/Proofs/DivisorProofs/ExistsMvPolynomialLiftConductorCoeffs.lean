import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mvPolynomial_lift_of_mem_conductor :
    ∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G := by
  intro R R' ν _ _ _ c hc G hG
  have key : ∀ z ∈ c.map (algebraMap R R'), ∃ y ∈ c, algebraMap R R' y = z := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ => ∃ y ∈ c, algebraMap R R' y = z)
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · exact ⟨0, c.zero_mem, map_zero _⟩
    · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, c.add_mem ha hb, map_add _ _ _⟩
    · rintro r _ _ ⟨a, ha, rfl⟩
      obtain ⟨y, hy, h⟩ := hc a ha r
      exact ⟨y, hy, by rw [h, smul_eq_mul, mul_comm]⟩
  rw [MvPolynomial.mem_map_C_iff] at hG
  choose y hy hyG using fun m => key _ (hG m)
  refine ⟨∑ m ∈ G.support, MvPolynomial.monomial m (y m), ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [MvPolynomial.map_monomial, Ideal.Quotient.eq_zero_iff_mem.mpr (hy m), map_zero]
  · rw [map_sum]
    conv_rhs => rw [G.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.map_monomial, hyG]

end GlobalTheory
