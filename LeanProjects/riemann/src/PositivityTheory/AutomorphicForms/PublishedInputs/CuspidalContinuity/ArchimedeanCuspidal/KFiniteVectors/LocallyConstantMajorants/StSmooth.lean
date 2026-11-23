import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth

noncomputable section

open MeasureTheory Matrix

namespace Ad3.K.LC

abbrev M23 : Type := Fin 2 → Fin 3 → ℂ
abbrev M22 : Type := Fin 2 → Fin 2 → ℂ

abbrev Sw : Type := SchwartzMap (M23 × (Fin 2 → ℂ)) ℂ

def blk (x : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 3) ℂ := !![1, 0, x 0; 0, 1, x 1]

def rowv (t y : ℂ) (h : Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → ℂ := Matrix.vecMul ![t, t * y] h⁻¹

def inn (Ψ : Sw) (g : GL (Fin 3) ℂ) (h : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) : ℂ :=
  ∫ p : (Fin 2 → ℂ) × ℂ, Ψ (Matrix.of.symm (h * blk p.1 * (g : Matrix (Fin 3) (Fin 3) ℂ)), rowv t p.2 h) *
    psiC (-(p.1 1)) * psiC (-p.2)

def ph (n : ℤ) (z : ℂ) : ℂ := (z / (‖z‖ : ℂ)) ^ n

def sec (k : ℕ) (Ψ : Sw) (g : GL (Fin 3) ℂ) : ℂ :=
  ((‖(g : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) *
    ∫ h : M22, (∫ t : ℂ, inn Ψ g (Matrix.of h) t * ph (4 * (k : ℤ) - 4) t) *
      ph (-(2 * (k : ℤ) - 2)) (Matrix.of h).det * ((‖(Matrix.of h).det‖ ^ (-(2 : ℝ)) : ℝ) : ℂ)

def StLin : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ Ψ : Sw) (c : ℂ),
  sec k (Φ + Ψ) = sec k Φ + sec k Ψ ∧ sec k (c • Φ) = c • sec k Φ

def StStable : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (h : GL (Fin 3) ℂ),
  ∃ Φ' : Sw, (fun g => sec k Φ (g * h)) = sec k Φ'

def StPsi : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (x y z : ℂ) (g : GL (Fin 3) ℂ),
  sec k Φ (uni x y z * g) = psiC (x + z) * sec k Φ g

def StCen : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (a : ℂˣ) (g : GL (Fin 3) ℂ), sec k Φ (dg a a a * g) = sec k Φ g

def StSmooth : Prop := ∀ k : ℕ, 3 ≤ k → ∀ Φ : Sw, SmoothC (sec k Φ)

def StDerCap : Prop := ∀ k : ℕ, 3 ≤ k → ∃ D D' : Fin 3 → Fin 3 → Module.End ℂ Sw,
  (∀ (Φ : Sw) (i j : Fin 3), derH i j (sec k Φ) = sec k (D i j Φ) ∧ derA i j (sec k Φ) = sec k (D' i j Φ)) ∧
  ∀ (Φ : Sw) (u : ℂ), sec k (Formalism.REAL.qdet D (u + 1) Φ) = ((u + (k - 1)) * u * (u - (k - 1))) • sec k Φ ∧
    sec k (Formalism.REAL.qdet D' (u + 1) Φ) = ((u + (k - 1)) * u * (u - (k - 1))) • sec k Φ

def StGauge : Prop := ∀ k : ℕ, 3 ≤ k → ∀ Φ : Sw, ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ (a b : ℂˣ), ∀ o ∈ U3,
  ‖sec k Φ (dg (a * b) b 1 * o)‖ ≤ C / (‖(a : ℂ)‖ * ‖(b : ℂ)‖) ^ T / ((1 + ‖(a : ℂ)‖) * (1 + ‖(b : ℂ)‖)) ^ N

def StInt : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (s : ℂ), 1 / 4 < s.re →
  Integrable (fun a => sec k Φ (dg a 1 1) * chC 0 (s - 1) a) mulC

def StInt' : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (s : ℂ), s.re < 3 / 4 →
  Integrable (fun p : ℂˣ × ℂ => sec k Φ (mm p.1 p.2) * chC 0 s p.1) (mulC.prod volC)

def StFe : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Φ : Sw) (n : ℤ) (s : ℂ), 1 / 4 < s.re → s.re < 3 / 4 →
  ∫ p : ℂˣ × ℂ, sec k Φ (mm p.1 p.2) * chC n s p.1 ∂(mulC.prod volC) =
    complexGL3 k n s * ∫ a, sec k Φ (dg a 1 1) * chC n (s - 1) a ∂mulC

def StKfin : Prop := ∀ k : ℕ, 3 ≤ k → ∃ Φ : Sw, sec k Φ ≠ 0 ∧
  FiniteDimensional ℂ (Submodule.span ℂ {W' | ∃ o ∈ U3, W' = fun g => sec k Φ (g * o)})

end Ad3.K.LC
