import Formalism.FilteredPoleLength.ReducedBasisBounds.ReductionQuotient

namespace Formalism.LatticeBaseChangeAlt

theorem ordCeil : OrdCeil := by
  intro n x h
  have h1 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  have h2 : (-(⌈x⌉ : ℝ) - 1) < (n : ℝ) := by linarith
  have h3 : (-⌈x⌉ - 1 : ℤ) < n := by exact_mod_cast h2
  omega

theorem poleOrderGood : PoleOrderGood := by
  intro ep T ν νs c' vet e hep hc hv hν ⟨n, hn⟩ he
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hint : (ep : ℝ) * ((T : ℝ) * ν - e) = (((T : ℤ) * n - ep * e : ℤ) : ℝ) := by
    push_cast; rw [← hn]; ring
  rw [hint, Int.ceil_intCast, Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · rw [← hint]
    have : (T : ℝ) * ν - e ≤ T * c' * vet := by nlinarith
    nlinarith

theorem poleOrderBad : PoleOrderBad := by
  intro ep T ν νs c' vet hep hT hc hv hν e
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have he : (T : ℝ) * (νs + 1) ≤ (e : ℝ) := Int.le_ceil _
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hx : (ep : ℝ) * ((T : ℝ) * ν - e) ≤ (ep : ℝ) * (T * c' * vet) - ep := by
    have : (T : ℝ) * ν - e ≤ T * c' * vet - 1 := by nlinarith
    nlinarith
  have hc1 : ((⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) < (ep : ℝ) * ((T : ℝ) * ν - e) + 1 :=
    Int.ceil_lt_add_one _
  rw [Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · nlinarith

theorem shareExponent : ShareExponent := by
  intro D T δ xL xF hδ h1 h2
  have hD : (0 : ℝ) ≤ D := by positivity
  nlinarith

theorem heightAbsorb : HeightAbsorb := by
  intro HL Hde X Y a ha ha2 hY h1 h2
  have hm : X ≤ max X 0 := le_max_left _ _
  have hm0 : 0 ≤ max X 0 := le_max_right _ _
  nlinarith

theorem filIntegerStep : FilIntegerStep := by
  intro νF νE T c φ μ h1 h2 h3
  have hT : (0 : ℝ) ≤ T := by positivity
  have : ((T : ℤ) * νE : ℤ) < νF := by
    have : ((T : ℝ) * νE) < νF := by nlinarith
    exact_mod_cast this
  omega

theorem sFChain : SFChain := by
  intro ξn lam d' ρ φ t p RR T c hξ hl hd hρ hφ hφ2 ht hRR hTc hc1
  have h1 : ξn ^ 2 * lam ^ 2 ≤ d' ^ 2 := by
    have : 0 ≤ ξn * lam := by positivity
    nlinarith
  have hξ2 : 0 < ξn ^ 2 := by positivity

  have h2 : 2 * (RR * (T * c)) * (d' ^ 2 * ρ) < ξn ^ 2 * p := by nlinarith
  have h3 : T * c ≤ RR * (T * c) := by nlinarith
  have h4 : (T * c) * (ξn ^ 2 * lam ^ 2 * ρ) ≤ (RR * (T * c)) * (d' ^ 2 * ρ) := by
    apply mul_le_mul h3 (mul_le_mul_of_nonneg_right h1 hρ) (by positivity) (by nlinarith)
  have h5 : (T * c) * (ξn ^ 2 * φ) ≤ (T * c) * (ξn ^ 2 * (2 * ρ * lam ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hφ2 hξ2.le) hTc
  have h6 : ξn ^ 2 * (T * c * φ) < ξn ^ 2 * p := by nlinarith
  exact lt_of_mul_lt_mul_left h6 hξ2.le

end Formalism.LatticeBaseChangeAlt
