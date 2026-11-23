import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TInj

section From

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W) (ω : W →+* V)
  {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (D : DegPre V)
  (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 T.B).left)
  (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull β₂))

def From : Prop :=
  IsGrpPullback D.P.A T.B (spMap ω) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (D.c a).left ≫ β = spMap ω ≫ (T.c₀ ((n : ℤ) • e a)).left) ∧
    ∀ a b, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧
      ∀ z J J', Good T.M.L z J → Good D.P.L z J' →
        val (D.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V).left) z ⊤ (unitOn k) *
          (lamVal w (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J J' *
            val (T.τ₀ ((n : ℤ) • e a) ((n : ℤ) • e b)) ((TK V).hom ≫ spMap ω) z J)

def TautPt (F : Type) [Field F] [Algebra (FractionRing V) F] (a : Fin T.r → ℤ) (g : GtPtF D F) : Prop :=
  g.b.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ a).left ∧
    ∀ χ, ∃ k : Fˣ, (k : F) = ∏ i, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (s i)) ^ ε i (e χ) a ∧
      ∀ z J J', Good T.M.L z J → Good D.P.L z J' →
        val (g.s χ) (𝟙 _) z J' = gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k) *
          (lamVal w (lift (DegPre.cF D F χ) g.b).left z J J' *
            val (T.τ₀ ((n : ℤ) • e χ) a) ((TF (R := V) F).hom ≫ spMap ω) z J)

end From

section Tr

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

def Ext (f : R →+* V) {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F]
    (j : F₀ →+* F) : Prop :=
  ∀ r, j (algebraMap (FractionRing R) F₀ (algebraMap R (FractionRing R) r)) =
    algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (f r))

theorem ext_id (F : Type) [Field F] [Algebra (FractionRing R) F] : Ext (RingHom.id R) (RingHom.id F) := fun _ => rfl

def Tr (f : R →+* V) {D₀ : DegPre R} {D : DegPre V} (hD : IsPullDeg f D₀ D) {F₀ F : Type} [Field F₀]
    [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F) (g₀ : GtPtF D₀ F₀) (g : GtPtF D F) :
    Prop :=
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  ∃ g₁ : GtPtF D₀ F, (g₁.b.left = spMap j ≫ g₀.b.left ∧
    ∀ χ, LB.Gen.Corr D₀.P.L _ _ _ _ (g₁.s χ) (LB.pullGen D₀.P.L _ _ (g₀.s χ) (spMap j))) ∧ IsPullGtF f hD F g₁ g

end Tr

def OverPt {X : Scheme.{0}} {h n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre h n ζ sX) {S : Scheme.{0}}
    (A : PolAV S) (y : S ⟶ X) (α : A.A.left ⟶ c.A.left) : Prop :=
  IsGrpPullback A.A c.A y α ∧ ∃ α₂ : (G2 A.A).left ⟶ (G2 c.A).left, IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (c.P.pull α₂)

def Match {V : Type} [CommRing V] [IsDomain V] (D₁ D₂ : DegPre V) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F]
    [Algebra (FractionRing V) F] : Prop :=
  IsMonHom b ∧ IsIso b ∧
    LBIso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₂.P.A D₂.P.L).pull
      (lift (fst D₁.P.A D₁.P.A ≫ b) (snd D₁.P.A D₁.P.A ≫ b) : G2 D₁.P.A ⟶ G2 D₂.P.A).left) ∧
    (∀ χ, ∃ u : LB.Gen (CmpLB D₁ D₂ b (φ.symm.toAddMonoidHom χ) χ), Nrm u) ∧
    ∀ (y : D₁.X) (g : GtPtF D₁ F), GtPtF.IsIota y g →
      ∃ g' : GtPtF D₂ F, Act D₁ D₂ b φ.symm.toAddMonoidHom g g' ∧ GtPtF.IsIota (φ y) g'

def QImg {V : Type} [CommRing V] [IsDomain V] {D₁ D₂ : DegPre V} (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) {F : Type} [Field F]
    [Algebra (FractionRing V) F] {k : ℕ} (p₁ : QkPt D₁ F k) (p₂ : QkPt D₂ F k) : Prop :=
  ∃ p' : QkPt D₂ F k, p'.y = φ p₁.y ∧ Act D₁ D₂ b φ.symm.toAddMonoidHom p₁.g p'.g ∧ QkPt.Equiv D₂ F p' p₂

end GlobalTheory.TInj
