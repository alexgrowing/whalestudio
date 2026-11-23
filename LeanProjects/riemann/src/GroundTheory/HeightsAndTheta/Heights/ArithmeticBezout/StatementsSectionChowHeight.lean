import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemConePointsSpanX0
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt)

open Classical in

def SectionChowHeight.Statement : Prop :=
  ∀ (n e δ : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (P : Ideal (MRing (PBlk n)))
    (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℚ) (u : Fin n → ℤ)
    (g : Ideal (MRing (PBlk n)) → MvPolynomial (Fin (e + 1) × Fin n) ℚ)
    (d : Ideal (MRing (PBlk n)) → ℕ),
    IsUnit S → IsArithVar P (e + 1 + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) (e + 1) δ
      (map (Rat.castHom ℂ) f) →
    IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
    (∀ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u), IsHorizontal W →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) e (d W)
        (map (Rat.castHom ℂ) (g W))) →
      IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (IndefiniteRowSideFullHecke.ArithBezout.specFirst (fun j => (u j : ℚ)) f) δ =
        ∑ᶠ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u),
          (multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
            (if IsHorizontal W then IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g W) (d W) else 0)

end GroundTheory.Heights₂.Heights
