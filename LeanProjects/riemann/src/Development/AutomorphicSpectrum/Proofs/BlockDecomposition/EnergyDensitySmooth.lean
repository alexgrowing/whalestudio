import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommuteStatement

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Sm.normSq {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {u : ℝ → Mat n → W} (hu : Sm u) : Sm fun s y => (‖u s y‖ ^ 2 : ℝ) := by
  have h := ContDiffOn.norm_sq ℝ (show ContDiffOn ℝ ∞ (Function.uncurry u) _ from hu)
  exact h.congr fun z _ => rfl

theorem Sm.inner {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {u v : ℝ → Mat n → W} (hu : Sm u) (hv : Sm v) : Sm fun s y => ⟪u s y, v s y⟫_ℝ := by
  have h := ContDiffOn.inner ℝ (show ContDiffOn ℝ ∞ (Function.uncurry u) _ from hu)
    (show ContDiffOn ℝ ∞ (Function.uncurry v) _ from hv)
  exact h.congr fun z _ => rfl

theorem Sm.add {n : ℕ} {f g : ℝ → Mat n → ℝ} (hf : Sm f) (hg : Sm g) :
    Sm fun s y => f s y + g s y := by
  have h := ContDiffOn.add (show ContDiffOn ℝ ∞ (Function.uncurry f) _ from hf)
    (show ContDiffOn ℝ ∞ (Function.uncurry g) _ from hg)
  exact h.congr fun z _ => rfl

theorem Sm.const_mul {n : ℕ} (c : ℝ) {f : ℝ → Mat n → ℝ} (hf : Sm f) :
    Sm fun s y => c * f s y := by
  have h := ContDiffOn.mul (contDiffOn_const (c := c))
    (show ContDiffOn ℝ ∞ (Function.uncurry f) _ from hf)
  exact h.congr fun z _ => rfl

theorem Sm.sum {n : ℕ} {ι : Type} (t : Finset ι) {f : ι → ℝ → Mat n → ℝ}
    (hf : ∀ i ∈ t, Sm (f i)) : Sm fun s y => ∑ i ∈ t, f i s y := by
  have h := ContDiffOn.sum (s := t) (f := fun i => Function.uncurry (f i))
    (fun i hi => show ContDiffOn ℝ ∞ (Function.uncurry (f i)) _ from hf i hi)
  exact h.congr fun z _ => by simp [Function.uncurry]

theorem sm_dens_inner {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (u : ℝ → Mat n → W) (hu : Sm u) :
    Sm (dens u) ∧ ∀ (X : Mat n) (v : ℝ → Mat n → W), Sm v →
      Sm fun s y => ⟪Rt X u s y, v s y⟫_ℝ := by
  obtain ⟨hdt, hRt, -⟩ := GlobalTheory.T.smooth_time_right_derivatives_commute u hu
  refine ⟨?_, fun X v hv => (hRt X).inner hv⟩
  exact (hdt.normSq.add (Sm.const_mul _ (Sm.sum _ fun p _ => (hRt (hm p)).normSq))).add hu.normSq

end GlobalTheory.CompanionTheory.WaveSpd
