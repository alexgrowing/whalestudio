import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRingEquivApplyEqMulOfTranscendental
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.JetAlg

variable {p : ℕ} [hp : Fact p.Prime]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem norm_sub_one_lt {y : ℂ_[p]} {k : ℕ} (h : y ^ p ^ k = 1) : ‖y - 1‖ < 1 := by
  have hne : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hy : ‖y‖ ≤ 1 := by
    have h1 : ‖y‖ ^ p ^ k = 1 := by rw [← norm_pow, h, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hne).1 h1).le
  let Y : ball p := ⟨y, hy⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out (Y - 1) 1 k
  have hr' := congrArg (fun t : ball p => (t : ℂ_[p])) hr
  simp only [sub_add_cancel, one_pow, mul_one] at hr'
  push_cast at hr'
  have hz : ‖y - 1‖ ≤ 1 := (Y - 1).2
  have hrr : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  have e : (y - 1) ^ p ^ k = -((p : ℂ_[p]) * (y - 1) * r) := by
    have : (Y : ℂ_[p]) = y := rfl
    rw [this, h] at hr'
    linear_combination -hr'
  have h2 : ‖(y - 1) ^ p ^ k‖ < 1 := by
    rw [e, norm_neg, norm_mul, norm_mul, mul_assoc]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_p_lt_one
      (mul_le_one₀ hz (norm_nonneg _) hrr)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hne).1 h2

theorem bd_derivative {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) : Bd 1 (derivative ℂ_[p] f) := by
  intro n
  rw [coeff_derivative, norm_mul]
  refine mul_le_one₀ (hf _) (norm_nonneg _) ?_
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n + 1)
  simpa using this

theorem bd_DT {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) : Bd 1 (DT f) := by
  have h := bd_derivative hf
  intro n
  rw [DT, add_mul, one_mul, map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h n) ?_)
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul]; exact h n

theorem bd_iterate {f : ℂ_[p]⟦X⟧} (hf : Bd 1 f) (k : ℕ) : Bd 1 (DT^[k] f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact bd_DT ih

theorem differentiable_U1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (U1 d x F) := by
  unfold U1 h1
  fun_prop

theorem differentiable_W1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (W1 d x F) := by
  have := differentiable_U1 d x hF
  unfold W1
  fun_prop

end GlobalTheory.MomOne.JetAlg

namespace GlobalTheory.MomOne
open JetAlg

theorem jets_algebraic : ∀ (d q : ℕ) [Fact q.Prime] (δ : ℂ) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsTh d θ → δ ≠ 0 → (∀ ι : ℂ ≃+* ℂ_[q], ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ) → ∀ (ι : ℂ ≃+* ℂ_[q]) (t y : ℂ) (n s k : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good ι d n s y → δ⁻¹ ^ k * iteratedDeriv k (W1 d y (U1 d t θ)) 0 ∈ algebraicClosure ℚ ℂ := by
  intro d q hq δ θ hd hd16 hsp hθ hδ hL ι t y n s k hs ht hy
  refine mem_algebraicClosure_of_norm_le q ι _ 1 ?_
  intro ι' hι'
  obtain ⟨Ω, hΩ, h1', h2', -⟩ := hL ι'
  obtain ⟨hA, hB, -⟩ := okArith d q ι hd hd16 hsp
  have hy' : Good ι' d n s y := by
    obtain ⟨v, hv, hn, rfl⟩ := hy
    refine ⟨v, hv, ?_, rfl⟩
    have hc : InOK d (conj v) := (hA.2.2 v v hv hv).2.2.2
    have := hι' ⟨conj v, (hB _ hc).2.2⟩
    simp only at this
    rw [this]; exact hn
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · exact absurd (by simpa using hs) hq.out.ne_one
    · exact h
  obtain ⟨hζ, hE⟩ := h2' t y n s hs ht hy'
  have hb := (Shift.shift_laws q _ (norm_sub_one_lt hζ)).1 _ _ (h1' t ⟨s, hs0, hs, ht⟩)
  rw [← hE] at hb
  have han : AnalyticAt ℂ (W1 d y (U1 d t θ)) 0 :=
    (differentiable_W1 d y (differentiable_U1 d t hθ.1)).analyticAt 0
  have hk := (hat_multiplicative_chart q ι' (Ω / ι' δ) _ han).2.1 k
  have hc := bd_iterate hb k 0
  rw [coeff_zero_eq_constantCoeff_apply, hk, div_eq_mul_inv, mul_pow, mul_assoc, norm_mul, norm_pow, hΩ,
    one_pow, one_mul] at hc
  rw [map_mul, map_pow, map_inv₀]
  exact hc

end GlobalTheory.MomOne
