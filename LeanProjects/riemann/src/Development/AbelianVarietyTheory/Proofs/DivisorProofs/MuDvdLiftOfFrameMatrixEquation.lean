import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdFrobXiSub
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem mu_dvd_of_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι κ : Type) [Fintype ι] (R S : Matrix ι ι F.B) (R0 S0 : Matrix ι ι (Ainf p O)) (Y : Matrix ι κ F.B) (F0 : Matrix ι κ (Ainf p O)), (∀ i j, F.τ ∣ R i j - F.a (R0 i j)) → (∀ i j, F.τ ∣ S i j - F.a (S0 i j)) → (∀ i m, F.τ ∣ Y i m - F.a (F0 i m)) → R * Y.map F.σ = S * Y → ∀ i m, Sandwich.mu ε ∣ (R0 * F0.map WittVector.frobenius - S0 * F0) i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F ι κ _ R S R0 S0 Y F0 hR hS hY hRS i m
  apply (F.a_dvd _).1
  set q := Ideal.Quotient.mk (Ideal.span {F.τ})
  have key : ∀ x y : F.B, F.τ ∣ x - y → q x = q y := fun x y h =>
    Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)
  have hR' : ∀ i j, q (R i j) = q (F.a (R0 i j)) := fun i j => key _ _ (hR i j)
  have hS' : ∀ i j, q (S i j) = q (F.a (S0 i j)) := fun i j => key _ _ (hS i j)
  have hY' : ∀ i m, q (Y i m) = q (F.a (F0 i m)) := fun i m => key _ _ (hY i m)
  have hYσ : ∀ i m, q (F.σ (Y i m)) = q (F.a (WittVector.frobenius (F0 i m))) := fun i m => by
    apply key
    rw [← F.σ_a, ← map_sub]
    exact tau_dvd_sigma F _ (hY i m)
  have h := congrArg (fun M => q (M i m)) hRS
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul] at h
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change q _ = 0
  rw [Matrix.sub_apply, map_sub, map_sub, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply]
  simp only [map_sum, map_mul, Matrix.map_apply, ← hR', ← hS', ← hYσ, ← hY']
  exact h

end GlobalTheory.WinLift
