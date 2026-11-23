import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def RadicalBaseChange.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (ι : Type)
    (I : Ideal (MvPolynomial ι K)), I.IsRadical → (I.map (MvPolynomial.map σ)).IsRadical

def ChowFormExtend.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (n k : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin k × Fin n) K),
    IsChowForm I k f → IsChowForm (I.map (MvPolynomial.map σ)) k (MvPolynomial.map σ f)

def ChowFormReduced.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) F))
    (h : MvPolynomial (Fin k × Fin n) F),
    IsHomogIdeal J → J.IsRadical → IsChowForm J k h → IsChowFormCycle (fundCycle J) k h

end

end GroundTheory.Heights₂.Heights
