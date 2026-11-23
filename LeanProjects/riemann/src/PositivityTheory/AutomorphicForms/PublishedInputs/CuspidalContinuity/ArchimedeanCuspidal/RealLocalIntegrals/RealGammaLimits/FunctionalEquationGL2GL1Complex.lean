import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Z2

noncomputable section

open MeasureTheory Complex

namespace Ad3.LR.C

def TateR : Prop := ∀ (f : SchwartzMap ℝ ℂ) (e : Bool) (s : ℂ), 0 < s.re → s.re < 1 →
  z1 (SchwartzMap.fourierTransformCLM ℂ f) e (1 - s) = gT e s * z1 f e s

def TateInt : Prop := ∀ (f : SchwartzMap ℝ ℂ) (e : Bool) (s : ℂ), 0 < s.re →
  Integrable (fun a : ℝˣ => f a * chR e s a) mulR

def FunctionalEquationGL2GL1Complex : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ (δ : Bool) (s : ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ), g.det ≠ 0 →
  0 < s.re → s.re < 1 → z2' k δ s g = g2 k s * z2 k δ s g

def GamSplit : Prop := ∀ (k : ℕ) (δ : Bool) (s : ℂ), 3 ≤ k → gamR k δ s = g2 k s * gT (!δ) s

end Ad3.LR.C
