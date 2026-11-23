import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Expand
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.DegPderivMul

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.PolyComp

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose MvPolynomial

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ}

def scalTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, inLie k r X) : DTerm k r Wp Wq where
  coef g := P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  coefAdj g := star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  word := w
  word_lie := hw
  adj_id := by
    intro x A B
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hsInner, PI.UnitaryGroupMassFormula.UsCompose.hsVec_smul,
      inner_smul_right, inner_smul_left, Complex.star_def, Complex.conj_conj]

end

end GlobalTheory.HatNF.PolyComp

namespace GlobalTheory.HatNF

open GlobalTheory.HatNF.PolyComp

end GlobalTheory.HatNF
