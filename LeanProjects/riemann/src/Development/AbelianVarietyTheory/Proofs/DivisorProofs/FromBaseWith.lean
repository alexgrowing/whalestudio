import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

def FromBaseWith {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : GlobalTheory.UChart.Gens Q) {W₀ : Type} [CommRing W₀]
    (ιb : W₀ →+* V) (B₀ : Over (Sp W₀)) [GrpObj B₀] (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left))
    (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
    (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)) : Prop :=
  IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧
    (∀ a, GlobalTheory.UChart.cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
    ∀ (a b : Q.X) zz (J : (Sp V ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Sp V ⟶ B₀.left) → M₀.ι),
      Good Q.P.L zz J → Good M₀ zz J₀ →
      val (τ₀ a b) (𝟙 (Sp V)) zz J =
        gm (GlobalTheory.UChart.cpt Q (a + b)) zz _
            (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q (a + b) ≫ β), J (GlobalTheory.UChart.cpt Q (a + b)))) *
        (gm (GlobalTheory.UChart.cpt Q a) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q a ≫ β), J (GlobalTheory.UChart.cpt Q a))))⁻¹ *
        (gm (GlobalTheory.UChart.cpt Q b) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q b ≫ β), J (GlobalTheory.UChart.cpt Q b))))⁻¹ *
        gm (GlobalTheory.UChart.cpt Q 0) zz _ (w.s (fun _ => J₀ (GlobalTheory.UChart.cpt Q 0 ≫ β), J (GlobalTheory.UChart.cpt Q 0))) *
        val (τ₁ a b) (spMap ιb) zz J₀

theorem fromBase_iff {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : GlobalTheory.UChart.Gens Q) {W₀ : Type}
    [CommRing W₀] (ιb : W₀ →+* V) :
    GlobalTheory.UChart.FromBase Q τ₀ ιb ↔ ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)), FromBaseWith Q τ₀ ιb B₀ M₀ c₀ τ₁ β w :=
  Iff.rfl

abbrev gwx {X' X Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (y : Y)
    (J : (Y ⟶ X') → L'.ι) (J₀ : (Y ⟶ X) → L.ι) (x : Y ⟶ X') : (Y.presheaf.stalk y)ˣ :=
  gw w x y (J₀ (x ≫ F)) (J x)

end GlobalTheory.USep.EvG
