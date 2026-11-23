import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TChart

def isoVal {S S₁ S' : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B₁]
    [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left} {M₁ : LB B₁.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {β₂' : (G2 B').left ⟶ (G2 B₁).left} (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂'))
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B₁.left) → M₁.ι) (J' : (Z ⟶ B.left) → M.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm p z _ (w.s (fun _ I => J (p ≫ β₂' ≫ (psum B₁ (x2 B₁) I.down).left),
    fun _ I => J' (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)))

def IsNormIso {R : Type} [CommRing R] [IsDomain R] {S S₁ : Scheme.{0}} {B : Over S} {B₁ : Over S₁} {B' : Over (Sp R)}
    [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj B'] {M : LB B.left} {M₁ : LB B₁.left}
    {β₂ : (G2 B').left ⟶ (G2 B).left} {β₂' : (G2 B').left ⟶ (G2 B₁).left}
    (w : LB.Iso ((abelian₂ B M).pull β₂) ((abelian₂ B₁ M₁).pull β₂')) : Prop :=
  ∀ z J J', Good M₁ z J → Good M z J' → isoVal w (lift (1 : TK R ⟶ B') (1 : TK R ⟶ B')).left z J J' = 1

def PeriodRel {o V V₁ W : Type} [CommRing o] [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing W]
    [IsLocalRing W] (D : DegPre V) (T : TautBase o W) (f₁ : V →+* V₁) (κ₁ : W →+* V₁) {B' : Over (Sp V₁)} [GrpObj B']
    {β₂ : (G2 B').left ⟶ (G2 D.P.A).left} {β₂' : (G2 B').left ⟶ (G2 T.B).left}
    (w : LB.Iso ((abelian₂ D.P.A D.P.L).pull β₂) ((abelian₂ T.B T.M.L).pull β₂')) (c : (Fin T.r → ℤ) ≃+ D.X)
    (x : (Fin T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')) (n : ℕ) (q : (Fin T.r → ℤ) → (Fin T.r → ℤ) → (FractionRing V₁)ˣ) :
    Prop :=
  ∀ κK : (TK V₁).left ⟶ (TK V).left, κK ≫ jK V = jK V₁ ≫ spMap f₁ → ∀ a b z J J', Good T.M.L z J → Good D.P.L z J' →
    val (D.tau (c a) (c b)) κK z J' = gm (𝟙 (TK V₁).left) z ⊤ (unitOn (q a b)) *
      (isoVal w (lift (toUnit (TK V₁) ≫ x a) (toUnit (TK V₁) ≫ x b)).left z J J' *
        val (T.τ₀ ((n : ℤ) • a) ((n : ℤ) • b)) ((TK V₁).hom ≫ spMap κ₁) z J)

end GlobalTheory.TChart
