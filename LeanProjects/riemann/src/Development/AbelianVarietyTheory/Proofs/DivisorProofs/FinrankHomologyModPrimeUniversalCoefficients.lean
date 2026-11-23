import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardQuotPrimeSmulEqCardKerMulPowFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyOfShortExactMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardZmodTensorEqCardQuotPrimeMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyRestrictScalarsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMulPrimeZmodTensorComplexStatement
open CategoryTheory Limits

namespace GlobalTheory

theorem uct_mod_p : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → (∀ n, Module.Finite ℤ (C.homology n)) → ∀ n : ℕ, (Module.finrank (ZMod p) ((((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))) - Module.finrank ℤ (C.homology (n + 1)) := by
  intro C p _ hinj hfin n
  obtain ⟨π, hz, hS⟩ := GlobalTheory.T.shortExact_mul_prime_zmod_tensor_complex C p hinj
  have e := GlobalTheory.T.natCard_homology_of_shortExact_mul' p C _ π hz hS n
  rw [GlobalTheory.T.natCard_homology_restrictScalars_alt] at e
  haveI := hfin n
  haveI := hfin (n + 1)
  have a1 := GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology n) p
  have a2 := GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology (n + 1)) p
  rw [← GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples] at a1 a2 e
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hcp : Nat.card (ZMod p) = p := by simp
  have c1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology n))
  have c2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology (n + 1)))
  rw [hcp] at c1 c2
  set D := (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n
  have hk : Nat.card (LinearMap.ker ((p : ℤ) • LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1))) ≠ 0 := by
    intro h0; rw [h0, zero_mul, c2] at a2; exact absurd a2 (pow_ne_zero _ (by omega))
  have hD : Nat.card D ≠ 0 := by
    rw [e, c1]; exact mul_ne_zero (pow_ne_zero _ (by omega)) hk
  haveI : Finite D := Nat.finite_of_card_ne_zero hD
  haveI : Module.Finite (ZMod p) D := Module.Finite.of_finite
  have c0 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := D)
  rw [hcp] at c0
  have key : p ^ (Module.finrank (ZMod p) D + Module.finrank ℤ (C.homology (n + 1))) = p ^ (Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1)))) := by
    rw [pow_add, pow_add, ← c0, e, ← c1, ← c2, a2]; ring
  have := Nat.pow_right_injective hp key
  push_cast; omega

end GlobalTheory
