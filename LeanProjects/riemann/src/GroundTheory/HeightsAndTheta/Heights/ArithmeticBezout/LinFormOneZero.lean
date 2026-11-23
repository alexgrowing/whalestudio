import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ImportsAlt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp Xc)

def GenericFibreIdeal.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MRing (PBlk n))), IsArithVar P d →
    IsProjPrime (genericIdeal P) ∧
      (genericIdeal P).comap (MvPolynomial.map (Int.castRingHom ℚ)) = IndefiniteRowSideFullHecke.ArithBezout.finIdeal P

def DivSuppHorizontalArithVar.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ) (H : Ideal (MRing (PBlk n))),
    IsArithVar P (d + 1) → IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
      H ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) → IsHorizontal H → IsArithVar H d

def IntChowFormExists.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n))), IsArithVar P (e + 1) →
    ∃ (δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℤ), IndefiniteRowSideFullHecke.ArithBezout.IsIntChowForm P e δ f

end ObjectsChow

end GroundTheory.Heights₂.Heights
