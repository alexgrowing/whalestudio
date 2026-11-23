import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

def IsDegZeroSmooth {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (u : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z

section

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isDegZeroSmooth_log {B : HermLine ι} (hB : IsSmoothHerm B) (h0 : B.a = 0) :
    IsDegZeroSmooth (fun z => Real.log (B.h z)) := by
  refine ⟨ContDiffOn.log hB fun z hz => (B.pos z hz).ne', fun c z hc => ?_⟩
  simp only [B.smul c z hc, h0, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]

theorem isDegZeroSmooth_const (a : ℝ) : IsDegZeroSmooth (ι := ι) (fun _ => a) :=
  ⟨contDiffOn_const, fun _ _ _ => rfl⟩

theorem IsDegZeroSmooth.mul {u v : ((Σ k, ι k) → ℂ) → ℝ} (hu : IsDegZeroSmooth u)
    (hv : IsDegZeroSmooth v) : IsDegZeroSmooth (fun z => u z * v z) :=
  ⟨hu.1.mul hv.1, fun c z hc => by simp only [hu.2 c z hc, hv.2 c z hc]⟩

end

def planeSq (z : (Σ k, PBlk 3 k) → ℂ) : ℝ := ∑ i : Fin 3, ‖z ⟨(), i⟩‖ ^ 2

def planeBump (z : (Σ k, PBlk 3 k) → ℂ) : ℝ :=
  Real.smoothTransition (4 * ‖z ⟨(), 0⟩‖ ^ 2 / planeSq z - 1)

end GroundTheory.Heights₂.Heights
