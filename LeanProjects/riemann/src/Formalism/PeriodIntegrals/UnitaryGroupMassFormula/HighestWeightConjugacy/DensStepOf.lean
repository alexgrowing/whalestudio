import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStep

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

open Classical in

def repPt {L : Type} [Field L] [NumberField L] {n : ℕ} (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) :
    (L →+* ℂ) × Fin n × Fin n → ℂ := fun p =>
  if p.1 = (InfinitePlace.mk p.1).embedding then Y (InfinitePlace.mk p.1) p.2.1 p.2.2
  else (Y (InfinitePlace.mk p.1))⁻¹ p.2.2 p.2.1

def DensA : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ γ₀ ∈ GQ0 L n, MvPolynomial.eval (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) F = 0) →
    ∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ, (∀ w, (Y w)ᴴ * Y w = 1) → (∀ w, (1 + Y w).det ≠ 0) →
      MvPolynomial.eval (repPt Y) F = 0

def DensB : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ, (∀ w, (Y w)ᴴ * Y w = 1) → (∀ w, (1 + Y w).det ≠ 0) →
      MvPolynomial.eval (repPt Y) F = 0) →
    ∀ y, InV y → MvPolynomial.eval y F = 0

theorem densStep_of (ha : DensA) (hb : DensB) : DensStep :=
  fun L _ _ _ n F h => hb L n F (ha L n F h)

end PI.UnitaryGroupMassFormula.HwConjInf
