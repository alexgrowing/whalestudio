import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.Trait

def Along {O' R : Type} [CommRing O'] [IsDomain O'] [CommRing R] [IsDomain R] (f : O' →+* R) (C : Type) [Field C]
    [Algebra (FractionRing O') C] [Algebra (FractionRing R) C] : Prop :=
  ∀ x, algebraMap (FractionRing R) C (algebraMap _ _ (f x)) = algebraMap (FractionRing O') C (algebraMap _ _ x)

def RatTors {R : Type} [CommRing R] [IsDomain R] (B : PolAV (Sp R)) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (n : ℕ) : Prop :=
  ∀ x : TF (R := R) C ⟶ B.A, x ^ n = 1 → ∃ x₀ : TK R ⟶ B.A, x.left = jFK (R := R) C ≫ x₀.left

def wVal {R O' : Type} [CommRing R] [IsDomain R] [CommRing O'] [IsDomain O'] {P : DegPre R} {D₀ : DegPre O'} {C : Type}
    [Field C] [Algebra (FractionRing R) C] [Algebra (FractionRing O') C] {N' N : NumD C} (ν' : NumOf P C N')
    (ν : NumOf D₀ C N) {ψ : P.P.A.left ⟶ D₀.P.A.left} (w : LB.Iso P.P.L (D₀.P.L.pull ψ)) (x : N'.A) : C :=
  valF (ν'.eA x).left _ (w.s (fun _ => ν.J ((ν'.eA x).left ≫ ψ), ν'.J (ν'.eA x).left)).val
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
  {a : ArcIn D l β O' b} {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing O') C]

def Labels (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) {o : Full D C} (M : Mdl o) {N' : NumD C} (ν' : NumOf M.P.D.toPre C N')
    (J : NumD.Iso (A.N.twist A.be u) N') (k : ℕ) : Prop :=
  ∀ x (p : (A.N.twist A.be u).QT k) (q' : N'.QT k) p' z, TwRel A.be u (r k) (A.q _ x) p →
    q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev k x).left ≫ M.φ →
    M.P.ToA C k p' z

def Fit (A : Lift a C) (u : Cˣ) {o : Full D C} (M : Mdl o) (f : O' →+* M.W) {N' : NumD C} (ν' : NumOf M.P.D.toPre C N')
    (J : NumD.Iso (A.N.twist A.be u) N') (ψ : M.P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (w : LB.Iso M.P.D.toPre.P.L (a.D₀.P.L.pull ψ)) (e : a.D₀.X ≃ₗ[𝓞 E] M.P.D.toPre.X) : Prop :=
  IsGrpPullback M.P.D.toPre.P.A a.D₀.P.A (spMap f) ψ ∧ w.IsGen ∧
    (∀ x : A.N.A, (ν'.eA (J.φ x)).left ≫ ψ = (A.ν.eA x).left) ∧ (∀ y : A.N.X, e (A.ν.eX y) = ν'.eX (J.e y)) ∧
    (∀ x, wVal ν' A.ν w x ≠ 0) ∧ ∀ x : A.N.A, (J.h x : C) * wVal ν' A.ν w (J.φ x) = wVal ν' A.ν w 1
end

def AllS (P : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
    (a : ArcIn D l β O' b) {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ)
    (_ : ℕ → Cˣ) {o : Full D C} (M : Mdl o) (_ : O' →+* M.W) {N' : NumD C} (_ : NumOf M.P.D.toPre C N'),
    NumD.Iso (A.N.twist A.be u) N' → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l)
    (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] (b : O →+* O')
    (a : ArcIn D l β O' b) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) (o : Full D C) (M : Mdl o)
    (f : O' →+* M.W) (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (J : NumD.Iso (A.N.twist A.be u) N'),
    Roots u r → Along f C → P a A u r M f ν' J
end GlobalTheory.Ex.Trait
end
