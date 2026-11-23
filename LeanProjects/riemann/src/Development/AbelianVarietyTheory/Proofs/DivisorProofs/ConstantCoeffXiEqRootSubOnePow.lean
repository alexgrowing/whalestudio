import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd

open Ideal WittVector Polynomial

namespace GlobalTheory.Sandwich

theorem charP_sub_one_pow_pred_eq_geom_sum {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    (x : R) : (x - 1) ^ (p - 1) = ∑ i ∈ Finset.range p, x ^ i := by
  have key : ((X : (ZMod p)[X]) - 1) ^ (p - 1) = ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i := by
    have h1 : ((X : (ZMod p)[X]) - 1) ^ p = (∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) *
        ((X : (ZMod p)[X]) - 1) := by
      rw [geom_sum_mul, sub_pow_char, one_pow]
    have h2 : ((X : (ZMod p)[X]) - 1) ^ p = ((X : (ZMod p)[X]) - 1) ^ (p - 1) *
        ((X : (ZMod p)[X]) - 1) := by
      rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]
    have hne : ((X : (ZMod p)[X]) - 1) ≠ 0 := X_sub_C_ne_zero 1
    exact mul_right_cancel₀ hne (h2.symm.trans h1)
  have := congrArg (eval₂RingHom (ZMod.castHom (dvd_refl p) R) x) key
  simpa [map_sum, map_pow, map_sub] using this

theorem constantCoeff_xi : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p),
    WittVector.constantCoeff (GlobalTheory.Sandwich.xi ε) = (GlobalTheory.Sandwich.root ε - 1) ^ (p - 1) := by
  intro p _ O _ _ _ ε
  rw [charP_sub_one_pow_pred_eq_geom_sum, xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

end GlobalTheory.Sandwich
