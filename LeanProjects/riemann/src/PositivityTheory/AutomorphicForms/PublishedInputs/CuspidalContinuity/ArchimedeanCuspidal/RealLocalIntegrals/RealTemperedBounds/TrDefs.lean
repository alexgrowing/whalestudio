import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.MatrixMulApply
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateTermsVanish

noncomputable section

open MeasureTheory Matrix

namespace Ad3.LR.DTr

def TrLim : Prop := ∀ (Ψ : Sw) (g : GL (Fin 3) ℝ) (a b : Fin 2) (w : M22 → ℂ),
  (∀ h : M22, (Matrix.of h).det < 0 → w h = 0) → ContDiffOn ℝ 1 w {h : M22 | 0 < (Matrix.of h).det} →
  Integrable (fun h : M22 => w h * inn Ψ g (Matrix.of h)) →
  Integrable (fun h : M22 => w h * inn (Rp a b Ψ) g (Matrix.of h)) →
  Integrable (fun h : M22 => Lop a b w h * inn Ψ g (Matrix.of h)) →
  ∫ h, w h * inn (Rp a b Ψ) g (Matrix.of h) = ∫ h, Lop a b w h * inn Ψ g (Matrix.of h)

def WeightVanishesNegDetSmoothPosDet : Prop := ∀ k : ℕ, 3 ≤ k →
  (∀ h : M22, (Matrix.of h).det < 0 → w0 k h = 0) ∧ ContDiffOn ℝ (⊤ : ℕ∞) (w0 k) {h : M22 | 0 < (Matrix.of h).det}

def DInt1 : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (v : ℂ) (a b : Fin 2) (Φ : Sw) (g : GL (Fin 3) ℝ),
  Integrable (fun h : M22 => Lt v a b (w0 k) h * inn Φ g (Matrix.of h))

end Ad3.LR.DTr
