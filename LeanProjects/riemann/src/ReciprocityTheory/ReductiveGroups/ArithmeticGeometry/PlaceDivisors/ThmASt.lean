import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace ReciprocityTheory.ChartRestriction.G.Pdiv
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

def ThmAGtStC (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
      (E : SplitExt (Spec (CommRingCat.of O))) (B : Out.PolAV (Spec (CommRingCat.of O)))
      (_ : B.A = E.B) (_ : HEq B.grp E.grpB) (G : Over (Spec (CommRingCat.of O))) [GrpObj G]
      [IsCommMonObj G],
      E.IsGt G → HTChar p v G

end ReciprocityTheory.ChartRestriction.G.Pdiv
