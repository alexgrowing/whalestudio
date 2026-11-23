import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerRealPlaces.RealZetaIntegralGL2
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bounds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding

noncomputable section
open MeasureTheory Matrix Complex
open Ad3 Ad3.LR Ad3.K.GL2LocalData Ad3.K.GL2LocalData.WR

namespace GlobalTheory.CompanionTheory.GL2LocalData.RD

def del : GL (Fin 2) ℝ := dg2 (-1) 1

def cst (k : ℕ) (n : ℤ) : ℂ := I ^ (jj n) * (-I) ^ (2 * k - 1 + mm k n)

open GlobalTheory.CompanionTheory.TateR in

def negE : (ℝˣ × ℝˣ × ℝ) ≃ᵐ (ℝˣ × ℝˣ × ℝ) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.mulRight (-1 : ℝˣ)) (MeasurableEquiv.refl _)

def Star : Prop := ∀ k : ℕ, 3 ≤ k → ∀ n : ℤ, ∀ Φ Φ₂, IsPhi k n Φ Φ₂ → ∀ t : GL (Fin 2) ℝ,
  dW3R (sec k Φ) (emR t) = cst k n * sec k Φ (emR (del * t))

def Jv (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![-y 1, y 0]

def sq (y : Fin 2 → ℝ) : ℝ := y 0 ^ 2 + y 1 ^ 2

def cols (a b : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a 0, b 0; a 1, b 1]

def fr (y : Fin 2 → ℝ) (D ρ : ℝ) : M22 := Matrix.of.symm (cols y ((D / sq y) • Jv y + ρ • y))

def Yc (y : Fin 2 → ℝ) : ℂ := (y 0 : ℂ) + I * (y 1 : ℂ)

def dotv (a b : Fin 2 → ℝ) : ℝ := a 0 * b 0 + a 1 * b 1

def gL (t : GL (Fin 2) ℝ) : GL (Fin 3) ℝ := w3R * emR (tinvR t)

def gR (t : GL (Fin 2) ℝ) : GL (Fin 3) ℝ := emR (del * t)

def Lin (n : ℤ) (t : GL (Fin 2) ℝ) (y : Fin 2 → ℝ) (E ρ : ℝ) : ℂ :=
  ∫ v : Fin 2 → ℝ, phi1 n (cols v ((E / sq y) • Jv y + ρ • y) * (tinvR t).val) *
    Complex.exp (2 * Real.pi * I * ((dotv (Jv y) v / E : ℝ) : ℂ))

def Pint (n : ℤ) (t : GL (Fin 2) ℝ) (y : Fin 2 → ℝ) (E : ℝ) : ℂ :=
  ∫ ρ : ℝ, Complex.exp (2 * Real.pi * I * (ρ : ℂ)) * Lin n t y E ρ

def Qfn (n : ℤ) (t : GL (Fin 2) ℝ) (y : Fin 2 → ℝ) (E ρ : ℝ) : ℂ :=
  phi1 n (cols ((1 / E) • Jv y) ((1 / sq y) • y - (ρ / E) • Jv y) * t.val)

def Qint (n : ℤ) (t : GL (Fin 2) ℝ) (y : Fin 2 → ℝ) (E : ℝ) : ℂ :=
  ∫ ρ : ℝ, Complex.exp (2 * Real.pi * I * (ρ : ℂ)) * Qfn n t y E ρ

end GlobalTheory.CompanionTheory.GL2LocalData.RD
