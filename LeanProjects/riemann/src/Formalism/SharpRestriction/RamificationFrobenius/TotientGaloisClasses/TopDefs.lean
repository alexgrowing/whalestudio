import Formalism.SharpRestriction.FamCore
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Landau

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.HC

theorem An.logDerivative_at_one_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : An.logDerivativeAtOne χ = GlobalTheoryTheory.logDerivativeAtOne χ := rfl

def EAt (Λ : Level) (D : D7) (x eps C : ℝ) : Prop := EAtH Λ D.host.toHostRaw D.host.TT x eps C

def EFamC (Λ : Level) {eps : ℝ} (Fm : FamCore eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, EAt Λ (Fm.D x i) x eps C

section

variable {Fam : ℝ → Type 1} (core : ∀ {eps : ℝ}, Fam eps → FamCore eps)
  (Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop)

def ChebyshevInequalityForFamily (Λ : Level) : Prop :=
  ∀ (eD eL eps : ℝ), 0 < eps → ∀ Fm : Fam eps, EFamC Λ (core Fm) →
    (∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, Tied Fm eD eL K cHH eK CL x) →
    ∃ x1 : ℝ, ∀ x ≥ x1, Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)

def ChebyshevInequalityEventual (Λ : Level) : Prop :=
  ∃ eD eL ε₁ : ℝ, 0 < ε₁ ∧ ∀ eps : ℝ, 0 < eps → eps < ε₁ → ∃ Fm : Fam eps, EFamC Λ (core Fm) ∧
    ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, Tied Fm eD eL K cHH eK CL x

variable {core Tied}

end

end Formalism.HC

end
