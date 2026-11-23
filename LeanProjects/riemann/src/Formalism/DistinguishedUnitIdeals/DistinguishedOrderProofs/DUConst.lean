import Mathlib
import Formalism.DistinguishedUnitIdeals.CoprimeProd
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GroundTheory

noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

section Helpers

variable {O : Type} [CommRing O] [IsDomain O]

theorem map_distinguished_eq_X_pow (ϖ : O) (E : Polynomial O)
    (hE : E.IsDistinguishedAt (Ideal.span {ϖ})) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (E : PowerSeries O) =
      X ^ E.natDegree := by
  ext n
  rw [coeff_map, Polynomial.coeff_coe, coeff_X_pow]
  rcases lt_trichotomy n E.natDegree with h | h | h
  · rw [if_neg h.ne]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hE.mem h)
  · rw [if_pos h, h, hE.monic.coeff_natDegree, map_one]
  · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero]

theorem map_unitDist (ϖ : O) (d : ℕ) (p : PowerSeries O) (hp : UnitDist ϖ d p) :
    ∃ U : PowerSeries (O ⧸ Ideal.span {ϖ}), IsUnit U ∧
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) p = U * X ^ d := by
  obtain ⟨u, E, hu, hE, hd, rfl⟩ := hp
  refine ⟨PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) u, hu.map _, ?_⟩
  rw [map_mul, map_distinguished_eq_X_pow ϖ E hE, hd]

theorem map_prod_unitDist (ϖ : O) (p : ℕ → PowerSeries O) (dg b : ℕ → ℕ) (I : Finset ℕ)
    (hp : ∀ s ∈ I, UnitDist ϖ (dg s) (p s)) :
    ∃ U : PowerSeries (O ⧸ Ideal.span {ϖ}), IsUnit U ∧
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (∏ s ∈ I, p s ^ b s) =
        U * X ^ (∑ s ∈ I, b s * dg s) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, isUnit_one, by simp⟩
  | insert t I ht ih =>
    obtain ⟨U, hU, hUe⟩ := ih (fun s hs => hp s (Finset.mem_insert_of_mem hs))
    obtain ⟨V, hV, hVe⟩ := map_unitDist ϖ (dg t) (p t) (hp t (Finset.mem_insert_self t I))
    refine ⟨V ^ b t * U, (hV.pow _).mul hU, ?_⟩
    rw [Finset.prod_insert ht, Finset.sum_insert ht, map_mul, hUe, map_pow, hVe, pow_add,
      mul_pow, ← pow_mul, mul_comm (dg t) (b t)]
    ring

end Helpers

theorem unit_constant_holds : DUConst := by
  intro O _ _ _ ϖ hϖ ℓ p I b g B y N c a hp hD h
  have hmax : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have : IsDomain (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  by_cases hc : c = 0
  · rw [hc]; exact dvd_zero _
  obtain ⟨v, w, hc'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  by_contra hy
  have hvy : v < y := by
    by_contra hvy
    apply hy
    rw [hc']
    exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (not_lt.mp hvy)) _
  set P := ∏ s ∈ I, p s ^ b s with hP
  set z := C (w : O) * P - C (ϖ ^ (y - v)) * a with hz
  have hz' : C (ϖ ^ (N + v)) * z ∈ Ideal.span {p g ^ B} := by
    have heq : C (ϖ ^ N) * (C c * P - C (ϖ ^ y) * a) = C (ϖ ^ (N + v)) * z := by
      rw [hz, hc']
      have hy' : y = v + (y - v) := by omega
      conv_lhs => rw [hy']
      simp only [map_mul, map_pow, pow_add]
      ring
    rw [← heq]; exact h
  have hzmem := mem_span_pow_of_uniformizer_mul O ϖ hϖ (ℓ ^ g) (p g) (hp g (Finset.mem_insert_self g I)) B (N + v)
    z hz'
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hzmem
  obtain ⟨U, hU, hUe⟩ := map_prod_unitDist ϖ p (fun s => ℓ ^ s) b I
    (fun s hs => hp s (Finset.mem_insert_of_mem hs))
  obtain ⟨V, -, hVe⟩ := map_unitDist ϖ (ℓ ^ g) (p g) (hp g (Finset.mem_insert_self g I))
  have hmap := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) hq
  have hzero : Ideal.Quotient.mk (Ideal.span {ϖ}) (ϖ ^ (y - v)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr (dvd_pow_self ϖ (by omega))
  rw [hz, map_sub, map_mul, map_mul, PowerSeries.map_C, PowerSeries.map_C, hzero, map_zero,
    zero_mul, sub_zero, hUe, map_mul, map_pow, hVe, mul_pow, ← pow_mul] at hmap
  have hW : IsUnit (C (Ideal.Quotient.mk (Ideal.span {ϖ}) (w : O)) * U) :=
    ((w.isUnit.map (Ideal.Quotient.mk (Ideal.span {ϖ}))).map C).mul hU
  set D := ∑ s ∈ I, b s * ℓ ^ s
  have hc1 := congrArg (coeff D) hmap
  have hlhs : coeff D (C (Ideal.Quotient.mk (Ideal.span {ϖ}) (w : O)) * (U * X ^ D)) =
      constantCoeff (C (Ideal.Quotient.mk (Ideal.span {ϖ}) (w : O)) * U) := by
    rw [← mul_assoc, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff]
  have hrhs : coeff D (V ^ B * X ^ (ℓ ^ g * B) *
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) q) = 0 := by
    have : V ^ B * X ^ (ℓ ^ g * B) * PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) q =
        X ^ (ℓ ^ g * B) * (V ^ B * PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) q) := by
      ring
    rw [this, coeff_X_pow_mul', if_neg (by rw [mul_comm]; omega)]
  rw [hlhs, hrhs] at hc1
  exact (isUnit_constantCoeff _ hW).ne_zero hc1

end Formalism.ExponentWindows
