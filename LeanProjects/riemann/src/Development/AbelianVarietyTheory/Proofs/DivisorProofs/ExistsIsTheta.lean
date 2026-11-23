import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

variable {V : Type} [CommRing V] [IsDomain V]

section Data

def IsTheta (D : DegPre V) (θ : D.SecB 1 0) : Prop :=
  ∀ (R' : Type) [CommRing R'] (f : V →+* R') θ',
    IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      ThetaOne.OneBasisAt D f θ'

theorem exists_isTheta [IsLocalRing V] (hV : IsCN V) (D : DegPre V) : ∃ θ, IsTheta D θ :=
  ThetaOne.exists_theta hV D

def UnitAt [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) : Prop :=
  ∃ J, Good D.P.L (Z := Sp V) (closedPoint V) J ∧
    IsUnit (sval (Z := Sp V) θ b.left (closedPoint V) J)

def IntFrm (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) {β : TF (R := V) (FractionRing V) ⟶ D.P.A}
    (w : Frm D (FractionRing V) 1 β) (l : FractionRing V) : Prop :=
  ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)), t.IsGen ∧
    ∀ z J, Good D.P.L z J → UT.cst (FractionRing V) z l * (val w (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val

def Exhausts (P : PolAV (Sp V)) (N : ℕ) {C : Type} (b : C → (𝟙_ (Over (Sp V)) ⟶ P.A)) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V) (p : Over.mk x ⟶ P.A), p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c

end Data

variable {I : Ideal V} {D : DegData V I} {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
  (U : UnifPre I D A G)

def Ext (x : TFK (R := V) (FractionRing V) ⟶ A.A) (h : 𝟙_ (Over (Sp V)) ⟶ G) : Prop :=
  x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = (toUnit (TF (R := V) (FractionRing V)) ≫ h).left

def FrRel (w₀ : W0 U) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp V)) ⟶ G)
    (l : FractionRing V) : Prop :=
  ∃ f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)), f.IsGen ∧
    ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG),
      Good A.L z JA → Good U.LG.L z JG →
      (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z
          (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left)).val *
        (val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA).val =
      UT.cst (FractionRing V) z l * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG).val

def Lies (w₀ : W0 U) (g' : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g'.b)
    (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ wk : Frm D.toPre (FractionRing V) k g'.b,
    (∀ z J, Good D.toPre.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k) → wk.IsGen →
    ∀ (s : SecA A (FractionRing V) k) (s' : Fam D.toPre (FractionRing V) k) (v : FractionRing V),
      U.ExpandsF (FractionRing V) k w₀ s s' → ValAt s x e v → SumF I (FractionRing V) (coef s' g' wk) v

end GlobalTheory.Poinc.IntTerm
