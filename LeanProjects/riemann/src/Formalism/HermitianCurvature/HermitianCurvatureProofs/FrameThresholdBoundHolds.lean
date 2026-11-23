import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings

namespace Formalism.FourierDecayAlt.P.PBD

open Formalism.FourierDecayAlt

def FrameThresholdBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) (w : ι),
    0 < G.g → 0 < G.lenI → 28 * Real.exp 1 ≤ C →
    (∀ one, 0 ≤ J.supA G de de' T T' l one w) →
    (∀ (b s : ℕ) (Q cg : ℝ), 1 ≤ b → 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg →
      cg ≤ (28 * G.N / G.lenI) ^ (2 * (b - 1) + s) →
      (2 * Real.pi / G.g) ^ (-(S6.nuBlock G.r b s)) * Q * cg *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w ≤
        J.thrS G C de de' T T' l b (s + 1) w) ∧
    (∀ (b : ℕ) (Q cg : ℝ), 1 ≤ b → 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg →
      cg ≤ (28 * G.N / G.lenI) ^ (2 * (b - 1)) →
      √((2 * Real.pi / G.g) ^ (-(2 * S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) * Q * cg *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) ≤
        J.thrP G C de de' T T' l b w)

theorem pow_bound (C x : ℝ) (n : ℕ) (hx : 0 ≤ x) (hC : 28 * Real.exp 1 ≤ C) :
    Real.exp 1 * (28 * x) ^ n ≤ C * (C * x) ^ n := by
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hC28 : (28 : ℝ) ≤ C := by nlinarith
  have heC : Real.exp 1 ≤ C := by nlinarith
  have hpow : (28 * x) ^ n ≤ (C * x) ^ n := pow_le_pow_left₀ (by positivity) (by nlinarith) n
  exact mul_le_mul heC hpow (by positivity) (by linarith)

theorem frame_threshold_bound : FrameThresholdBound := by
  intro ι _ G C de de' T T' l w hg hI hC hA
  have hN : 0 ≤ G.N := by unfold Sz.Glob.N; positivity
  have hkg : 0 < 2 * Real.pi / G.g := by positivity
  have key : ∀ (n : ℕ) (Q cg : ℝ), 0 ≤ Q → Q ≤ Real.exp 1 → 0 ≤ cg → cg ≤ (28 * G.N / G.lenI) ^ n →
      Q * cg ≤ C * (C * (G.N / G.lenI)) ^ n := by
    intro n Q cg h0 h1 h2 h3
    have hx : 0 ≤ G.N / G.lenI := div_nonneg hN hI.le
    rw [mul_div_assoc] at h3
    calc Q * cg ≤ Real.exp 1 * (28 * (G.N / G.lenI)) ^ n := mul_le_mul h1 h3 h2 (by positivity)
      _ ≤ C * (C * (G.N / G.lenI)) ^ n := pow_bound C _ n hx hC
  refine ⟨fun b s Q cg hb h0 h1 h2 h3 => ?_, fun b Q cg hb h0 h1 h2 h3 => ?_⟩
  · have hA' := hA (decide (b = 1 ∧ s + 1 = 1))
    have hk := key (2 * (b - 1) + s) Q cg h0 h1 h2 h3
    have hz : (2 * Real.pi / G.g) ^ (-(S6.nuBlock G.r b s)) =
        (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hkg.ne']
      congr 1
      unfold S6.nuBlock
      omega
    have hn : 2 * (b - 1) + (s + 1) - 1 = 2 * (b - 1) + s := by omega
    unfold J.thrS Sz.lamThreshold Sz.Glob.m
    rw [hn, hz, show C * (2 * Real.pi / G.g) * G.N / G.lenI = (C * (G.N / G.lenI)) * (2 * Real.pi / G.g) by ring,
      mul_pow]
    have hP : 0 ≤ (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
        J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w := mul_nonneg (by positivity) hA'
    calc (2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * Q * cg *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w
        = ((2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) * (Q * cg) := by ring
      _ ≤ ((2 * Real.pi / G.g) ^ (2 * (b - 1) + s) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) * (C * (C * (G.N / G.lenI)) ^ (2 * (b - 1) + s)) :=
          mul_le_mul_of_nonneg_left hk hP
      _ = C * (((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * J.supA G de de' T T' l (decide (b = 1 ∧ s + 1 = 1)) w) *
          ((C * (G.N / G.lenI)) ^ (2 * (b - 1) + s) * (2 * Real.pi / G.g) ^ (2 * (b - 1) + s)) := by ring
  · have hA' := hA false
    have hk := key (2 * (b - 1)) Q cg h0 h1 h2 h3
    have hz : (2 * Real.pi / G.g) ^ (-(2 * S6.nuBlock G.r b ((G.r : ℤ) + 2 - b))) =
        (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hkg.ne']
      congr 1
      unfold S6.nuBlock
      omega
    unfold J.thrP Sz.lamPrimeSq Sz.Glob.m
    apply Real.sqrt_le_sqrt
    rw [hz, show C * G.N / G.lenI = C * (G.N / G.lenI) by ring]
    have hP : 0 ≤ (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
        J.supA G de de' T T' l false w * (√(T * T'))⁻¹ := mul_nonneg (mul_nonneg (by positivity) hA') (by positivity)
    calc (2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * Q * cg *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹
        = ((2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) * (Q * cg) := by ring
      _ ≤ ((2 * Real.pi / G.g) ^ (2 * b - 1) * ((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ *
          J.supA G de de' T T' l false w * (√(T * T'))⁻¹) * (C * (C * (G.N / G.lenI)) ^ (2 * (b - 1))) :=
          mul_le_mul_of_nonneg_left hk hP
      _ = C * (((2 * Real.pi / G.g) ^ (2 * G.r + 2 - 1))⁻¹ * J.supA G de de' T T' l false w) *
          (2 * Real.pi / G.g) ^ (2 * b - 1) * (√(T * T'))⁻¹ * (C * (G.N / G.lenI)) ^ (2 * (b - 1)) := by ring

end Formalism.FourierDecayAlt.P.PBD

theorem Formalism.FourierDecayAlt.P.frame_threshold_bound_holds : Formalism.FourierDecayAlt.P.PBD.FrameThresholdBound := Formalism.FourierDecayAlt.P.PBD.frame_threshold_bound
