import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKSChart

section Data

variable {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R)
  (gam : Fin m → LinearMap.BilinForm ℤ Q.X)

def constHom {k : Type} [Field k] (ρ : R →+* DualNumber k) : R →+* DualNumber k :=
  (algebraMap k (DualNumber k)).comp ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)

def IsUnitPart (y : Q.X) (n : Fin m → ℕ)
    (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c y).left) fun _ => -1)) : Prop :=
  ψ₀.IsGen ∧ (∀ i, gam i y y = 2 * n i) ∧ ∃ e : (FractionRing R)ˣ,
    (e : FractionRing R) = algebraMap R _ (∏ i, t i ^ n i) ∧ ∀ z J, Good Q.P.L z J →
      val (Q.psi y) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn e) * val ψ₀ (toUnit (TK R)).left z J

def IsConstAlong {k : Type} [Field k] (ρ : R →+* DualNumber k) (a : Fin m → k) : Prop :=
  ∃ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ Q.P.A.left)
    (w : LB.Iso (Q.P.L.pull π₁) (Q.P.L.pull π₂)) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)) (ℓ : Q.X →+ k)
    (κ : (DualNumber k)ˣ),
    IsGrpPullback B' Q.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ ∧
    (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) ∧
    w.IsGen ∧ (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) ∧
    ∀ y n ψ₀, IsUnitPart Q t gam y n ψ₀ → ∀ e : (DualNumber k)ˣ,
      (e : DualNumber k) = 1 + TrivSqZeroExt.inr (∑ i, a i * n i + ℓ y) → ∀ z J, Good Q.P.L z J →
        val ψ₀ (spMap ρ) z J =
          gm (c' y) z _ (w.s (fun _ => J (c' y ≫ π₂), fun _ => J (c' y ≫ π₁))) *
            gm (𝟙 (Sp (DualNumber k))) z ⊤ (unitOn (κ * e)) * val ψ₀ (spMap (constHom ρ)) z J

def IsRigid [IsLocalRing R] : Prop :=
  ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin m → k), (∀ r ∈ maximalIdeal R, (ρ r).fst = 0) →
    (∀ i, ρ (t i) = 0) → IsConstAlong Q t gam ρ a → ∀ r, (ρ r).snd = 0

end Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HasRigidChart (Z : Model Xo c β) (x : gen Z) : Prop :=
  ∃ (k : Type) (_ : Field k) (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Z) (t : SAB H (Sp (ChartRing k m d)))
    (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → levelForms H l.M' P.D.toPre.X),
    ξ (closedPoint _) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    (FinalTheorems.stalkId (genBdIdeal Z) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom =
      Ideal.span {∏ i, bdParam k m d i} ∧
    (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Z ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) ∧
    Nonempty (SABMap t Z.t (ξ ≫ genι Z)) ∧
    IsMonomial P.D.toPre (bdParam k m d) (fun i => gam i) ∧ IsPartOfBasis gam ∧
    IsRigid P.D.toPre (bdParam k m d) (fun i => gam i)

def RigidForFan : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
        ∃ (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d k : ℕ), 1 ≤ d ∧ 1 ≤ k ∧
          SmoothOfRelativeDimension Dw.dim (genStr Y) ∧ FinalTheorems.Snc (genBdIdeal Y) ∧
          (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) ∧
          (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) ∧
          ((GlobalTheory.FlagMod.detOm Y).IsLB → GlobalTheory.IsAmpleLB (GlobalTheory.TorRef.polOf Y k BD)) ∧
          ∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x

end GlobalTheory.LogKSChart
