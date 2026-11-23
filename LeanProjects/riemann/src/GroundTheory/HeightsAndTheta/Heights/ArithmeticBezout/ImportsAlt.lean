import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsMultiHomogOfIsChowForm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal)

def ComplexChowFormToChowForm.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsArithVar P (e + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ g →
      ∃ c : ℂ, c ≠ 0 ∧ ∃ f : MvPolynomial (Fin (e + 1) × Fin n) ℚ,
        g = C c * map (Rat.castHom ℂ) f ∧ IsChowForm (genericIdeal P) (e + 1) f

def ChowFormToComplexChowForm.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
    IsArithVar P (e + 1) → IsChowForm (genericIdeal P) (e + 1) f → IsMultiHomog δ f →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
        (map (Rat.castHom ℂ) f)

open Classical in

def DivCycleGeneric.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ),
    IsArithVar P (e + 1) → IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
      divCycle (genericIdeal P) (fun j => (u j : ℚ)) =
        ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)).filter IsHorizontal).mapDomain
          genericIdeal

def VertPartEq.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ),
    IsArithVar P (e + 1) → IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
      vertTerm (genericIdeal P) (e + 1) (fun j => ((u j : ℤ) : 𝓞 ℚ)) =
        IndefiniteRowSideFullHecke.ArithBezout.vertPart P e (IndefiniteRowSideFullHecke.ArithBezout.linForm u)

end ObjectsChow

end GroundTheory.Heights₂.Heights
