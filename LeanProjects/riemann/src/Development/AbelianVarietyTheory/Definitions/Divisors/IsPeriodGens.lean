import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev prj {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {θ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
    (h : IsPullDeg θ D D') : D'.P.A.left ⟶ D.P.A.left :=
  h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf θ)

def Carry {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {θ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
    (h : IsPullDeg θ D D') {F : Type} [Field F] [Algebra (FractionRing R') F] (κ : FractionRing R →+* F) {k : ℕ}
    (p₀ : QkPt D (FractionRing R) k) (p : QkPt D' F k) : Prop :=
  h.xe p.y = p₀.y ∧ ∀ χ : D'.X, GenRel (F := F) h.w (p.g.s χ) (LB.pullGen _ _ _ (p₀.g.s (h.xe χ)) (spMap κ)) 1

def Extends {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (θ : R →+* R') {F : Type} [Field F]
    [Algebra (FractionRing R') F] (κ : FractionRing R →+* F) : Prop :=
  ∀ r : R, κ (algebraMap R (FractionRing R) r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (θ r))

def LinPull {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {θ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
    [Module (𝓞 E) D.X] [Module (𝓞 E) D'.X] (o : letI := H.starRing; D.OAct (𝓞 E)) (o' : letI := H.starRing; D'.OAct (𝓞 E))
    (h : IsPullDeg θ D D') : Prop :=
  (∀ (x : 𝓞 E) y, h.xe (x • y) = x • h.xe y) ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.onB.act x).left ≫ prj h = prj h ≫ (o.onB.act x).left)

structure Cmp {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (Q : DegPre R) [Module (𝓞 E) Q.X]
    (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (θ₁ θ₂ : R →+* R') (k : ℕ) where

  Q' : DegPre R'
  [mod : Module (𝓞 E) Q'.X]

  o' : letI := H.starRing; Q'.OAct (𝓞 E)
  bimult : Q'.TauBimult

  h₁ : IsPullDeg θ₁ Q Q'

  h₂ : IsPullDeg θ₂ Q Q'
  lin₁ : LinPull oQ o' h₁
  lin₂ : LinPull oQ o' h₂
  tors : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R') F] (κ₁ κ₂ : FractionRing R →+* F),
    Extends θ₁ κ₁ → Extends θ₂ κ₂ → ∀ (p₀ : QkPt Q (FractionRing R) k) (p₁ p₂ : QkPt Q' F k),
      Carry h₁ κ₁ p₀ p₁ → Carry h₂ κ₂ p₀ p₂ → QkPt.Equiv Q' F p₁ p₂

attribute [instance] Cmp.mod

variable {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V]
  (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I]
  (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X)

def DivBy (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g)) : Prop :=
  (∀ y, (((g y)⁻¹ : (FractionRing V)ˣ) : FractionRing V) =
      ∏ k, algebraMap V (FractionRing V) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y))) ∧
    (∀ y : Q.X, hD.xe y = e y) ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (oQ.onB.act x).left ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) ≫ (L.oa.onB.act x).left)

theorem divFrom_iff : DivFrom L Q oQ iw s ε e ↔ ∃ g hD, DivBy L Q oQ iw s ε e g hD := Iff.rfl

variable {Q} {g : Q.X → (FractionRing V)ˣ} (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g))

def IsDivPt (τ₁ : Gens L.D) (p : QkPt Q (FractionRing V) l.M') : Prop :=
  ∀ χ : Q.X, GenRel (F := FractionRing V) (B := Q.P.A.left) (B₀ := L.D.P.A.left) (M := Q.P.L) (M₀ := L.D.P.L)
    (φ := hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw)) hD.w (p.g.s χ)
    (LB.pullGen _ _ _ (τ₁ (l.M' • e χ) (e p.y)) (jK V ≫ spMap iw))
    (∏ k, algebraMap V (FractionRing V) (s k) ^ ε k (e χ) (e p.y))

def IsLevPt (a : D'.La) (p : QkPt Q (FractionRing V) l.M') : Prop :=
  p.y = 0 ∧ p.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) : Q.P.A.left ⟶ L.D.P.A.left) =
    jK V ≫ spMap iw ≫ (L.o.etaA a).left ≫ L.φB

def IsPeriodGens {W : Type} [CommRing W] [IsDomain W] (D : DegPre W) (τ₁ : Gens D) : Prop :=
  ∀ a b, (τ₁ a b).IsGen ∧ ∀ (z : (TK W).left) (J : ((TK W).left ⟶ D.P.A.left) → D.P.L.ι),
    Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ₁ a b) (toUnit (TK W)).left z J

end GlobalTheory.UCanon
