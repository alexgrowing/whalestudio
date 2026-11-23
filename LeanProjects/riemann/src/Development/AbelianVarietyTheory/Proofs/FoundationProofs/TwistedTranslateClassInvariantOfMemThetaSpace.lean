import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem ee_intCast_half (n : ℤ) : ee ((n : ℝ) / 2) = (-1 : ℂ) ^ n := by
  unfold ee
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem al_of_qH (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (m : ℤ) (h : qH D T x = m) :
    al D T x = (-1 : ℂ) ^ m := by
  unfold qH at h
  unfold al
  rw [h, round_intCast]

theorem qH_add_im (D : D7) (T : Tor D) {N N' : ℕ} (y u : VC D N N') :
    qH D T (y + u) - qH D T y - qH D T u + (Hf D T y u).im = 2 * (Hf D T (w0 D • y) u).im := by
  unfold qH
  rw [Hf_smul_left, Hf_add_left, Hf_add_right, Hf_add_right, Hf_conj D T y u]
  have h1 : (w0 D).re = 1 / 2 := by simp [w0]
  have h2 : (w0 D).im = Real.sqrt D.host.d / 2 := by simp [w0]
  simp only [Complex.add_re, Complex.conj_re, Complex.mul_im, h1, h2]
  ring

theorem repInd_of_thSp (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ : AddSubgroup (VC D N N'))
    (F : VC D N N' → ℂ) (hq : ∀ x ∈ A₂, ∃ m : ℤ, qH D T x = m)
    (hw : ∀ x ∈ A₂, ∀ y ∈ A₂, ∃ m : ℤ, (Hf D T (w0 D • x) y).im = m) (hF : F ∈ ThSp D T A₁) :
    RepInd D T A₁ A₂ F := by
  intro x hx y hy hxy
  have hu2 : x - y ∈ A₂ := A₂.sub_mem hx hy
  obtain ⟨u, rfl⟩ : ∃ u, x = y + u := ⟨x - y, by abel⟩
  rw [add_sub_cancel_left] at hxy hu2
  obtain ⟨a, ha⟩ := hq _ hx
  obtain ⟨b, hb⟩ := hq _ hy
  obtain ⟨c, hc⟩ := hq _ hu2
  obtain ⟨k, hk⟩ := hw _ hy _ hu2
  have h1 := qH_add_im D T y u
  rw [ha, hb, hc, hk] at h1
  have h2 : -(Hf D T y u).im = ((a - b - c - 2 * k : ℤ) : ℝ) := by push_cast; linarith
  funext z
  have h3 := U_U D T y u F z
  rw [h2, ee_intCast_half] at h3
  have h4 : al D T u * U D T y (U D T u F) z = U D T y F z := by
    have := hF.2 u hxy (z + y)
    conv_lhs => rw [U]
    conv_rhs => rw [U]
    rw [← mul_assoc, this]
  unfold aU
  rw [← h4, h3, al_of_qH D T _ _ ha, al_of_qH D T _ _ hb, al_of_qH D T _ _ hc, ← mul_assoc,
    ← mul_assoc, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
  congr 1
  have : b + c + (a - b - c - 2 * k) = a + 2 * (-k) := by ring
  rw [this, zpow_add₀ (by norm_num), zpow_mul]
  norm_num

end GlobalTheory.ThetaConj
