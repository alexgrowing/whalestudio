import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.AbLaw

def AlgSt : Prop := ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R →
  IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))),
    (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Smooth (Y e).hom) →
    (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) →
    ∃ (B : Over (Spec (CommRingCat.of R))) (M : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left),
      IsProjBy B.hom ∧ Smooth B.hom ∧ M.IsLB ∧ RelAmple B M ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧
      (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e))

def MorAlgSt : Prop := ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R →
  IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y Z : Over (Spec (CommRingCat.of R))), IsProjBy Y.hom → IsProjBy Z.hom → Smooth Y.hom →
    ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Z.left, (∀ e, f e ≫ Z.hom = (fstG I e Y).left ≫ Y.hom) →
    (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃! g : Y ⟶ Z, ∀ e, (fstG I e Y).left ≫ g.left = f e

def SecAlgSt : Prop := ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ N : LB Y.left, N.IsLB → ∀ f : ∀ e, LB.Sec (N.pull (fstG I e Y).left), (∀ e z J, Good N z J → sval (f (e + 1)) (thickMap R I e Y) z J = sval (f e) (𝟙 _) z J) → ∃! s : LB.Sec (N.pull (𝟙 Y.left)), ∀ e z J, Good N z J → sval s (fstG I e Y).left z J = sval (f e) (𝟙 _) z J

def PicardZeroDegenerationCondition : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (P : PolAV (Spec (CommRingCat.of A)))
  (O : LB P.A.left), O.IsLB → (∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) →
  ∃ x : 𝟙_ _ ⟶ P.A, LBIso O (LB.LinComb P.L (K := Fin 2) ![((toUnit P.A ≫ x) * 𝟙 P.A).left, 𝟙 P.A.left] ![1, -1])

def Ega : Prop := AlgSt ∧ MorAlgSt ∧ SecAlgSt ∧ PicardZeroDegenerationCondition
end GlobalTheory.LN
end
