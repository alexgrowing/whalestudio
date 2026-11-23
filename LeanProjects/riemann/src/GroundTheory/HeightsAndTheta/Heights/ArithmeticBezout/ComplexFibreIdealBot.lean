import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

def complexFibreIdeal {n : ℕ} (P : Ideal (MRing (PBlk n))) : Ideal (MvPolynomial (Fin n) ℂ) :=
  (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map (MvPolynomial.map (Int.castRingHom ℂ))

def ComplexFibreCycle.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsArithVar P (e + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ f →
      (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, IsProjPrime W) ∧
      IsChowFormCycle (fundCycle (complexFibreIdeal P)) (e + 1) f ∧
      ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.specFirst u f ≠ 0 ↔
        ∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W

end GroundTheory.Heights₂.Heights
