import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction

open Formalism.FourierDecayAlt.ThreeDimData

namespace GlobalTheory.GapSizeCheck

theorem gapOK_inhabited (k r : ℕ) (hk : 1 ≤ k) : ∃ h : ℝ, GapOK k r h := by
  set B : ℝ := |2 * Mexp r * (AS k r + AG k r) + AG k r + 3| +
    |9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3| +
    120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 with hB
  have hs : 1 ≤ 8 * Real.sqrt (2 * ((r : ℝ) + 1)) := by
    have : (1 : ℝ) ≤ Real.sqrt (2 * ((r : ℝ) + 1)) := by
      rw [Real.one_le_sqrt]; have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
    linarith
  have h1 := abs_nonneg (2 * Mexp r * (AS k r + AG k r) + AG k r + 3)
  have h2 := abs_nonneg (9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3)
  have h3 : (0 : ℝ) ≤ 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by positivity
  have h1' := le_abs_self (2 * Mexp r * (AS k r + AG k r) + AG k r + 3)
  have h2' := le_abs_self (9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3)
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have ha : aOf r (B * (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) = B := by
    unfold aOf; field_simp
  refine ⟨B * (8 * Real.sqrt (2 * ((r : ℝ) + 1))), hk, ?_, ?_, ?_⟩
  · nlinarith
  · rw [ha]; linarith
  · rw [ha]; linarith

theorem thresholds (k r : ℕ) (h : ℝ) (hg : GapOK k r h) :
    AG k r < (aOf r h - 1) / 2 ∧ AS k r < (aOf r h - 1) / 2 ∧
      (2 * Mexp r * AS k r + 1) + AG k r + 1 ≤ aOf r h - 1 := by
  obtain ⟨hk, -, h3, -⟩ := hg
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hG0 : 0 ≤ AG k r := by unfold AG; positivity
  have hd0 : 0 ≤ dN k r := by unfold dN; nlinarith [mul_nonneg hr hk0]
  have hS0 : 0 ≤ AS k r := by unfold AS; positivity
  have hM : 2 ≤ Mexp r := by unfold Mexp; nlinarith
  have e1 : 2 * AS k r ≤ Mexp r * AS k r := mul_le_mul_of_nonneg_right hM hS0
  have e2 : 2 * AG k r ≤ Mexp r * AG k r := mul_le_mul_of_nonneg_right hM hG0
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

theorem decay_range (k r : ℕ) (h : ℝ) (h120 : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) :
    120 * ((2 * r + k + 1 : ℕ) : ℝ) * (((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1)) ≤ h := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs : Real.sqrt ((r : ℝ) + 1) ≤ (r : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn1 : (r : ℝ) + 1 ≤ n := by rw [hn]; push_cast; linarith
  have : ((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1) ≤ n * n :=
    mul_le_mul hn1 (hs.trans hn1) (Real.sqrt_nonneg _) (by linarith)
  nlinarith

open scoped InnerProductSpace in

def KFinDecay {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ u v : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ u → PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v →
    ∃ C : ℝ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖⟪v, σ x u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN x ^ (-a)

def KFinDecayOfGap : Prop :=
  ∀ (k r : ℕ), 1 ≤ k → ∀ (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
    120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h → KFinDecay (k := k) (r := r) σ (aOf r h)

open scoped InnerProductSpace in

def SmoothDecayOfKFin : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (a : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → KFinDecay (k := k) (r := r) σ a →
    ∀ v0 : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v0 →
      ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
        ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          ‖⟪v0, σ x w⟫_ℂ‖ ≤
            C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum * Formalism.FourierDecayAlt.B.gN x ^ (1 - a)

end GlobalTheory.GapSizeCheck
