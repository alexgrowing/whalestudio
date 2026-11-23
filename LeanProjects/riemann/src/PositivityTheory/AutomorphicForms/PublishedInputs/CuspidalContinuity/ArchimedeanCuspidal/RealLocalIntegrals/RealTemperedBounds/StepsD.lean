import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.CrdTemperate

noncomputable section

open MeasureTheory Matrix LineDeriv

namespace Ad3.LR

def Rc (a b : Fin 2) : Sw →L[ℂ] Sw :=
  ∑ c : Fin 3, (SchwartzMap.smulLeftCLM ℂ (crd a c)).comp (lineDerivOpCLM ℂ Sw (eU b c))

def Rp (a b : Fin 2) : Module.End ℂ Sw := (Rc a b).toLinearMap

def rpol (a b : Fin 2) (h : M22) : M22 := fun r c => if r = b then h a c else 0

def w0 (k : ℕ) (h : M22) : ℂ :=
  Wm k (Matrix.of h)⁻¹ * sg (Matrix.of h).det * ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

def secW (w : M22 → ℂ) (Φ : Sw) (g : GL (Fin 3) ℝ) : ℂ :=
  sg (g : Matrix (Fin 3) (Fin 3) ℝ).det * ((|(g : Matrix (Fin 3) (Fin 3) ℝ).det| : ℝ) : ℂ) *
    ∫ h : M22, w h * inn Φ g (Matrix.of h)

def Lop (a b : Fin 2) (w : M22 → ℂ) (h : M22) : ℂ :=
  -(fderiv ℝ w h (rpol a b h)) - 2 * (if a = b then w h else 0)

def Lt (v : ℂ) (a b : Fin 2) (w : M22 → ℂ) (h : M22) : ℂ := (if a = b then v * w h else 0) + Lop a b w h

def gauF (k : ℕ) (X : M23) : ℂ :=
  ((X 0 0 : ℂ) + (X 1 0 : ℂ) * Complex.I) ^ (2 * k - 1) * Complex.exp (-(Real.pi : ℂ) * ∑ r, ∑ c, ((X r c : ℝ) : ℂ) ^ 2)

def DCap1 : Prop := ∀ (u : ℂ) (Φ : Sw), Formalism.REAL.qdet Dp (u + 1) Φ = u • Formalism.REAL.qdet Rp (u + 2) Φ

def QuantumDeterminantTwoExpansion : Prop := ∀ (A : Type) [Ring A] [Algebra ℂ A] (E : Fin 2 → Fin 2 → A) (v : ℂ),
  Formalism.REAL.qdet E v = Formalism.REAL.Tm E v 0 0 * Formalism.REAL.Tm E (v - 1) 1 1 - Formalism.REAL.Tm E v 1 0 * Formalism.REAL.Tm E (v - 1) 0 1

def DSecW : Prop := ∀ (k : ℕ) (Φ : Sw), sec k Φ = secW (w0 k) Φ

def HeckeOperatorSectionCompat : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (v : ℂ) (a b : Fin 2) (Ψ : Sw) (g : GL (Fin 3) ℝ),
  secW (w0 k) (Formalism.REAL.Tm Rp v a b Ψ) g = secW (Lt v a b (w0 k)) Ψ g

def TwoHeckeOperatorsSectionCompat : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (v v' : ℂ) (a b c d : Fin 2) (Ψ : Sw) (g : GL (Fin 3) ℝ),
  secW (Lt v' c d (w0 k)) (Formalism.REAL.Tm Rp v a b Ψ) g = secW (Lt v a b (Lt v' c d (w0 k))) Ψ g

def DQw : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (v : ℂ) (h : M22), (Matrix.of h).det ≠ 0 →
  Lt (v - 1) 1 1 (Lt v 0 0 (w0 k)) h - Lt (v - 1) 0 1 (Lt v 1 0 (w0 k)) h = ((v - 2) ^ 2 - ((k : ℂ) - 1) ^ 2) * w0 k h

def DInt2 : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (v v' : ℂ) (a b c d : Fin 2) (Φ : Sw) (g : GL (Fin 3) ℝ),
  Integrable (fun h : M22 => Lt v a b (Lt v' c d (w0 k)) h * inn Φ g (Matrix.of h))

def DNull : Prop := volume {h : M22 | (Matrix.of h).det = 0} = 0

def DDer : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (i j : Fin 3), der i j (sec k Φ) = sec k (Dp i j Φ)

def DGau : Prop := ∀ k : ℕ, ∃ Φ : Sw, ∀ X, Φ X = gauF k X

def DKne : Prop := ∀ k : ℕ, 3 ≤ k → ∀ Φ : Sw, (∀ X, Φ X = gauF k X) → sec k Φ ≠ 0

def DKfd : Prop := StLin → ∀ k : ℕ, 3 ≤ k → ∀ Φ : Sw, (∀ X, Φ X = gauF k X) →
  FiniteDimensional ℂ (Submodule.span ℂ {W' | ∃ o ∈ O3, W' = fun g => sec k Φ (g * o)})

end Ad3.LR
