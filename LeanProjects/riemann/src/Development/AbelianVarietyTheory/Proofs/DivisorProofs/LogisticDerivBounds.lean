import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

namespace GlobalTheory.InterpCurv

theorem scaled_logistic_deriv_bounds :
    ∀ (κ t σ ρ : ℝ), 0 < κ → 0 ≤ t → t ≤ 1 → 0 < σ → σ < 1 → 0 ≤ ρ → |t * (-κ * σ * (1 - σ))| + |t * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ))| ≤ (κ + κ ^ 2) * (1 - t * σ) ∧ |t * (-κ * σ * (1 - σ))| + |t * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ))| ≤ (κ + κ ^ 2) * (t * σ + ρ * (1 - t * σ)) ∧ (t * (-κ * σ * (1 - σ))) ^ 2 ≤ (κ + κ ^ 2) * (t * σ) * (t * σ + ρ * (1 - t * σ)) := by
  intro κ t σ ρ hκ ht0 ht1 hσ0 hσ1 hρ
  have h1σ : 0 ≤ 1 - σ := by linarith
  have hb : 0 ≤ t * σ := mul_nonneg ht0 hσ0.le
  have hbσ : t * σ ≤ σ := by nlinarith
  have hb1 : 0 ≤ 1 - t * σ := by linarith
  have ha : 0 ≤ t * σ * (1 - σ) := mul_nonneg hb h1σ
  have hk2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  have hK : 0 ≤ κ + κ ^ 2 := by linarith
  have e1 : |t * (-κ * σ * (1 - σ))| = κ * (t * σ * (1 - σ)) := by
    have : t * (-κ * σ * (1 - σ)) = -(κ * (t * σ * (1 - σ))) := by ring
    rw [this, abs_neg, abs_of_nonneg (mul_nonneg hκ.le ha)]
  have e2 : |t * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ))| ≤ κ ^ 2 * (t * σ * (1 - σ)) := by
    have : t * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ)) = (κ ^ 2 * (t * σ * (1 - σ))) * (1 - 2 * σ) := by
      ring
    rw [this, abs_mul, abs_of_nonneg (mul_nonneg hk2 ha)]
    have h : |1 - 2 * σ| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    exact mul_le_of_le_one_right (mul_nonneg hk2 ha) h
  have hsum : |t * (-κ * σ * (1 - σ))| + |t * (κ ^ 2 * σ * (1 - σ) * (1 - 2 * σ))|
      ≤ (κ + κ ^ 2) * (t * σ * (1 - σ)) := by
    rw [e1]; nlinarith
  have hab : t * σ * (1 - σ) ≤ t * σ := mul_le_of_le_one_right hb (by linarith)
  have ha1 : t * σ * (1 - σ) ≤ 1 - t * σ := by
    have h1 : t * σ * (1 - σ) ≤ 1 - σ := mul_le_of_le_one_left h1σ (by linarith)
    linarith
  have hρb : 0 ≤ ρ * (1 - t * σ) := mul_nonneg hρ hb1
  refine ⟨hsum.trans (mul_le_mul_of_nonneg_left ha1 hK),
    hsum.trans (mul_le_mul_of_nonneg_left (by linarith) hK), ?_⟩
  have e3 : (t * (-κ * σ * (1 - σ))) ^ 2 = κ ^ 2 * ((t * σ * (1 - σ)) * (t * σ * (1 - σ))) := by
    ring
  have h4 : (t * σ * (1 - σ)) * (t * σ * (1 - σ)) ≤ (t * σ) * (t * σ + ρ * (1 - t * σ)) :=
    mul_le_mul hab (by linarith) ha hb
  rw [e3, mul_assoc (κ + κ ^ 2)]
  exact mul_le_mul (by linarith) h4 (mul_nonneg ha ha) hK

end GlobalTheory.InterpCurv
