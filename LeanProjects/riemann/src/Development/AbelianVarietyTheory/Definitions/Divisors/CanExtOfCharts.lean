import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CanExtM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {V : X.Opens}

def IsBdd (c : Chart t V) (h : HdR c.A) : Prop :=
  ∃ v, IsTanAtG t (chart c.U) v ∧ c.HasImage h v

def canSet {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : Chart t V) : Set (HdR c.A) :=
  {h | IsBdd c h ∧ ∀ D ∈ logDer s (Scheme.IdealSheafData.vanishingIdeal V.compl) c.U, ∀ D' : Derivation ℤ c.S c.S,
    (∀ r, D' (algebraMap Γ(X, c.U.1) c.S r) = algebraMap Γ(X, c.U.1) c.S (D r)) → ∀ k, IsNabla D' h k → IsBdd c k}

def canLat {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : Chart t V) : Submodule Γ(X, c.U.1) (HdR c.A) :=
  Submodule.span Γ(X, c.U.1) (canSet s c)

def IsCanAt {K : Type} [CommRing K] (s : X ⟶ Sp K) (t : SAB H X) (V : X.Opens) (x : X) : Prop :=
  ∃ c : Chart t V, x ∈ c.U.1 ∧ IsCanLattice s c (canLat s c)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {cf : Coeff l}

def GoodModel (Y : Model Xo cf (RingHom.id cf.F)) : Prop :=
  SmoothOfRelativeDimension Dw.dim Y.s ∧ ReciprocityTheory.AnForm.R.FinalTheorems.Snc (boundary Y) ∧ HasLogKS Y.t Y.s (interior Y) ∧
    ∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChart Y x

def CanExtOfCharts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), GoodModel Y →
      ∃ L : ∀ ch : Chart Y.t (interior Y), Submodule Γ(Y.X, ch.U.1) (HdR ch.A), IsCanExt Y.s L

end GlobalTheory.CanExtM
