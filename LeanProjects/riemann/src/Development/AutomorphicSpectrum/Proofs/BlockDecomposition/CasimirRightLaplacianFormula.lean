import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FderivZeroApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RdSkewEqConst
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem sk_skew {n : ℕ} (p : Ix n) : (sk p)ᴴ = -sk p := by
  obtain ⟨b, i, j⟩ := p
  have hc : ∀ (a b : Fin n) (c : ℂ), (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
    intro a b c
    ext x y
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : a = y <;> by_cases h2 : b = x <;> simp [h1, h2]
  cases b
  · simp [sk, Matrix.conjTranspose_add, hc, Matrix.single_neg, add_comm]
  · simp [sk, Matrix.conjTranspose_sub, hc]

theorem Rd_Rd_of_act {n : ℕ} (E : KMod n) (Y : Mat n) (B : E.V →L[ℂ] E.V)
    (hB : ∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y f g = B (f g)) (f : Mat n → E.V) (hf : f ∈ CE E)
    (g : Mat n) (hg : g ∈ GLs n) : Rd Y (Rd Y f) g = B (B (f g)) := by
  have hnhds : GLs n ∈ nhds g := isOpen_GLs.mem_nhds hg
  have hev : Rd Y f =ᶠ[nhds g] (B.restrictScalars ℝ) ∘ f := by
    filter_upwards [hnhds] with y hy
    simpa using hB f hf y hy
  have hd : DifferentiableAt ℝ f g :=
    (hf.1.contDiffAt hnhds).differentiableAt (by simp)
  have hfd : fderiv ℝ (Rd Y f) g = (B.restrictScalars ℝ).comp (fderiv ℝ f g) := by
    rw [hev.fderiv_eq]
    exact ((B.restrictScalars ℝ).hasFDerivAt.comp g hd.hasFDerivAt).fderiv
  have h1 : Rd Y (Rd Y f) g = B (Rd Y f g) := by
    change fderiv ℝ (Rd Y f) g (g * Y) = B (fderiv ℝ f g (g * Y))
    rw [hfd]
    rfl
  rw [h1, hB f hf g hg]

theorem om_section {n : ℕ} (E : KMod n) : ∃ A : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n,
    Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g) := by
  choose B hB using fun p : Ix n => rd_skew_eq_const E (sk p) (sk_skew p)
  refine ⟨-(1 / 4 : ℂ) • ∑ p, B p * B p, fun f hf g hg => ?_⟩
  rw [OmDec.Om_eq_squares f hf.1 g hg, sub_eq_add_neg]
  congr 1
  have h : ∀ p, Rd (sk p) (Rd (sk p) f) g = B p (B p (f g)) := fun p =>
    Rd_Rd_of_act E (sk p) (B p) (hB p) f hf g hg
  simp only [h, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.neg_apply, neg_smul]
  rfl

end GlobalTheory.CompanionTheory.WaveSpd
