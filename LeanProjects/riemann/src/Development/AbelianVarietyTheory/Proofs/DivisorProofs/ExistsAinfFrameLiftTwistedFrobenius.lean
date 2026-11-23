import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxStep
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FLam

theorem exists_fixed {B : Type} [CommRing B] (q : B) [h : IsAdicComplete (Ideal.span {q}) B]
    (σ : B →+* B) (hσ : σ q = q) (w : B) : ∃ c : B, c = -w + q * σ c := by
  first
  | exact @_root_.GlobalTheory.FixedPointApproximation.exists_fixed
  | exact _root_.GlobalTheory.FixedPointApproximation.exists_fixed
  | (apply _root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FixedPointApproximation.exists_fixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FixedPointApproximation.exists_fixed ..)

theorem one_add_pow_of_sq {B : Type} [CommRing B] (x : B) (hx : x * x = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination (n : B) * hx

theorem frobenius_mu (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = (Sandwich.mu ε + 1) ^ p - 1 := by
  unfold Sandwich.mu
  rw [WittVector.frobenius_eq_map_frobenius, map_sub, map_one, WittVector.map_teichmuller,
    frobenius_def, map_pow]
  ring

theorem σ_τ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} (F : BFrame ε) :
    F.σ F.τ = p * F.τ := by
  have tf : ∀ x : F.B, (p : F.B) * x = 0 → x = 0 := by
    intro x hx
    have h1 : (p : F.Q) * algebraMap F.B F.Q x = 0 := by
      rw [← map_natCast (algebraMap F.B F.Q), ← map_mul, hx, map_zero]
    have h2 := (F.frame.unit_p.mul_right_eq_zero).1 h1
    exact F.frame.inj (by rw [h2, map_zero])
  apply sub_eq_zero.1
  apply tf
  have e1 : (p : F.B) * F.σ F.τ = F.a (WittVector.frobenius (Sandwich.mu ε)) := by
    rw [← F.σ_a, ← F.p_τ, map_mul, map_natCast]
  have e2 : F.a (WittVector.frobenius (Sandwich.mu ε)) = p * (p * F.τ) := by
    have hsq : (p * F.τ) * (p * F.τ) = 0 := by
      rw [show (p : F.B) * F.τ * (p * F.τ) = p * p * (F.τ * F.τ) by ring, F.τ_sq, mul_zero]
    rw [frobenius_mu, map_sub, map_pow, map_add, map_one, ← F.p_τ, add_comm,
      one_add_pow_of_sq _ hsq]
    ring
  rw [mul_sub, e1, e2, sub_self]

end GlobalTheory.FLam

open GlobalTheory.FLam in

theorem GlobalTheory.FLam.exists_lam : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ u : F.B, F.τ ∣ u - 1 → ∃ l : F.B, F.τ ∣ l - 1 ∧ F.σ l = u * l := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F u hu
  obtain ⟨w, hw⟩ := hu
  haveI : IsAdicComplete (Ideal.span {(p : F.B)}) F.B := F.frame.complete
  obtain ⟨c, hc⟩ := exists_fixed (p : F.B) F.σ (map_natCast F.σ p) w
  refine ⟨1 + F.τ * c, ⟨c, by ring⟩, ?_⟩
  have hu' : u = 1 + F.τ * w := by rw [← hw]; ring
  rw [map_add, map_one, map_mul, σ_τ, hu']
  have hτ := F.τ_sq
  linear_combination (-(w * c)) * hτ - F.τ * hc
