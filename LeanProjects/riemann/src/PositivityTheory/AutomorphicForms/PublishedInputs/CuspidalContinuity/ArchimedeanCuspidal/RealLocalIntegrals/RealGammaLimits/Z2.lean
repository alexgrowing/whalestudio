import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth

noncomputable section

open MeasureTheory Complex

namespace Ad3.LR.C

def z1 (f : ℝ → ℂ) (e : Bool) (s : ℂ) : ℂ := ∫ a : ℝˣ, f a * chR e s a ∂mulR

def gT (e : Bool) (s : ℂ) : ℂ :=
  (if e then -I else 1) * Gammaℝ (1 - s + if e then 1 else 0) / Gammaℝ (s + if e then 1 else 0)

def d2 (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, 1]

def w2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

def z2 (k : ℕ) (δ : Bool) (s : ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ∫ a : ℝˣ, Wm k (d2 a * g) * chR δ (s - 1 / 2) a ∂mulR

def z2' (k : ℕ) (δ : Bool) (s : ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ∫ a : ℝˣ, Wm k (d2 a * w2 * g) * chR (!δ) (1 / 2 - s) a ∂mulR

def g2 (k : ℕ) (s : ℂ) : ℂ := (-I) ^ (2 * k - 1) * Gammaℂ (1 - s + k - 1) / Gammaℂ (s + k - 1)

end Ad3.LR.C
