import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.InnW

noncomputable section

open MeasureTheory Matrix

namespace Ad3.K.LC.C

def GamSplit : Prop := ∀ (k : ℕ) (n : ℤ) (s : ℂ), complexGL3 k n s = g2 k n s * gC n s

def TateFunctionalEquationComplex : Prop := ∀ (f : ℂ → ℂ) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 → Integrable f →
  Integrable (fun w => f w * ((‖w‖ ^ (2 * (s.re - 1)) : ℝ) : ℂ)) →
  Integrable (fun r => fC f r * ((‖r‖ ^ (-2 * s.re) : ℝ) : ℂ)) →
  z1 (fC f) (-n) (1 - s) = gC n s * z1 f n s

def SlS : Prop := ∀ (Ψ : Sw) (X : M23), ∃ f : SchwartzMap (Fin 2 → ℂ) ℂ, ⇑f = sl Ψ X

def FunctionalEquationGL2GL1Complex : Prop := ∀ (k : ℕ), 3 ≤ k → ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ) (n : ℤ) (s : ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ),
  g.det ≠ 0 → 0 < s.re → s.re < 1 → z2' k n s f g = g2 k n s * z2 k n s f g

def SectionWhittakerFubini : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (g : GL (Fin 3) ℂ),
  sec k Ψ g = ((‖(g : Matrix (Fin 3) (Fin 3) ℂ).det‖ ^ 2 : ℝ) : ℂ) * ∫ h : M22, innW k Ψ g h 1

end Ad3.K.LC.C
