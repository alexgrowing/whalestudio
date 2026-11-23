import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

namespace GlobalTheory

theorem weight_bound_algebra :
    ∀ (K₁ A N f f1 f2 ρ a l : ℝ), 0 ≤ K₁ → 0 ≤ A → 0 ≤ N → 0 ≤ f → f < 1 → 0 ≤ ρ → 0 ≤ a →
      a ^ 2 ≤ A * N ^ 2 → |l| ≤ A * N ^ 2 → |f1| + |f2| ≤ K₁ * (1 - f) →
      |f1| + |f2| ≤ K₁ * (f + ρ * (1 - f)) → f1 ^ 2 ≤ K₁ * f * (f + ρ * (1 - f)) →
      |f1| * a ≤ K₁ * (A + √A + 1) * (1 - f) * N ∧
      (|f1| * a) ^ 2 ≤ K₁ * (A + √A + 1) * N ^ 2 * f * (f + ρ * (1 - f)) ∧
      |f1 * l + f2 * a ^ 2| ≤ K₁ * (A + √A + 1) * N ^ 2 * (f + ρ * (1 - f)) ∧
      |f1 * l + f2 * a ^ 2| ≤ K₁ * (A + √A + 1) * N ^ 2 * (1 - f) := by
  intro K₁ A N f f1 f2 ρ a l hK hA hN hf hf1 hρ ha ha2 hl hs1 hs2 hf1sq
  have hsA : 0 ≤ √A := Real.sqrt_nonneg A
  have h1f : 0 ≤ 1 - f := by linarith
  have hg : 0 ≤ f + ρ * (1 - f) := by positivity
  have hC : A ≤ A + √A + 1 := by linarith
  have hC' : √A ≤ A + √A + 1 := by linarith
  have haN : a ≤ √A * N := by
    have : a = √(a ^ 2) := (Real.sqrt_sq ha).symm
    rw [this, ← Real.sqrt_sq hN, ← Real.sqrt_mul hA]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have habs1 : |f1| ≤ K₁ * (1 - f) := by linarith [abs_nonneg f2]
  have hN2 : 0 ≤ N ^ 2 := by positivity
  have hAN : 0 ≤ A * N ^ 2 := by positivity

  have hkey : |f1 * l + f2 * a ^ 2| ≤ (|f1| + |f2|) * (A * N ^ 2) := by
    calc |f1 * l + f2 * a ^ 2| ≤ |f1 * l| + |f2 * a ^ 2| := abs_add_le _ _
      _ = |f1| * |l| + |f2| * a ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ a ^ 2)]
      _ ≤ |f1| * (A * N ^ 2) + |f2| * (A * N ^ 2) := by
          gcongr
      _ = (|f1| + |f2|) * (A * N ^ 2) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc |f1| * a ≤ (K₁ * (1 - f)) * (√A * N) :=
          mul_le_mul habs1 haN ha (by positivity)
      _ = √A * (K₁ * (1 - f) * N) := by ring
      _ ≤ (A + √A + 1) * (K₁ * (1 - f) * N) :=
          mul_le_mul_of_nonneg_right hC' (by positivity)
      _ = K₁ * (A + √A + 1) * (1 - f) * N := by ring
  · have hkf : 0 ≤ K₁ * f * (f + ρ * (1 - f)) := by positivity
    calc (|f1| * a) ^ 2 = f1 ^ 2 * a ^ 2 := by rw [mul_pow, sq_abs]
      _ ≤ (K₁ * f * (f + ρ * (1 - f))) * (A * N ^ 2) :=
          mul_le_mul hf1sq ha2 (by positivity) hkf
      _ = A * (K₁ * N ^ 2 * f * (f + ρ * (1 - f))) := by ring
      _ ≤ (A + √A + 1) * (K₁ * N ^ 2 * f * (f + ρ * (1 - f))) :=
          mul_le_mul_of_nonneg_right hC (by positivity)
      _ = K₁ * (A + √A + 1) * N ^ 2 * f * (f + ρ * (1 - f)) := by ring
  · calc |f1 * l + f2 * a ^ 2| ≤ (|f1| + |f2|) * (A * N ^ 2) := hkey
      _ ≤ (K₁ * (f + ρ * (1 - f))) * (A * N ^ 2) := mul_le_mul_of_nonneg_right hs2 hAN
      _ = A * (K₁ * N ^ 2 * (f + ρ * (1 - f))) := by ring
      _ ≤ (A + √A + 1) * (K₁ * N ^ 2 * (f + ρ * (1 - f))) :=
          mul_le_mul_of_nonneg_right hC (by positivity)
      _ = K₁ * (A + √A + 1) * N ^ 2 * (f + ρ * (1 - f)) := by ring
  · calc |f1 * l + f2 * a ^ 2| ≤ (|f1| + |f2|) * (A * N ^ 2) := hkey
      _ ≤ (K₁ * (1 - f)) * (A * N ^ 2) := mul_le_mul_of_nonneg_right hs1 hAN
      _ = A * (K₁ * N ^ 2 * (1 - f)) := by ring
      _ ≤ (A + √A + 1) * (K₁ * N ^ 2 * (1 - f)) :=
          mul_le_mul_of_nonneg_right hC (by positivity)
      _ = K₁ * (A + √A + 1) * N ^ 2 * (1 - f) := by ring

end GlobalTheory
