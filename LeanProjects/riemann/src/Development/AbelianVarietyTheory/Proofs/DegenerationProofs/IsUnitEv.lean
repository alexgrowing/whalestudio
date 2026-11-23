import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}}

def ev (g : Sp R ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V) : Γ(Y, V) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (g.appLE V ⊤ h).hom

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in

theorem _root_.GlobalTheory.SS.WtRat.ev_congr {g g' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y} (e : g = g') (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev g V h u = _root_.GlobalTheory.SS.WtRat.ev g' V h' u := by
  subst e
  rfl

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in

theorem _root_.GlobalTheory.SS.WtRat.ev_appLE (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (φ : Y ⟶ Y') (V : Y'.Opens)
    (W : Y.Opens) (e : W ≤ φ ⁻¹ᵁ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ V) (u : Γ(Y', V)) :
    _root_.GlobalTheory.SS.WtRat.ev g W h ((φ.appLE V W e).hom u) =
      _root_.GlobalTheory.SS.WtRat.ev (g ≫ φ) V h' u := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in

theorem _root_.GlobalTheory.SS.WtRat.ev_res (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) {V W : Y.Opens} (e : W ≤ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ g ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev g W h ((Y.presheaf.map (homOfLE e).op).hom u) =
      _root_.GlobalTheory.SS.WtRat.ev g V h' u := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in

theorem _root_.GlobalTheory.SS.WtRat.ev_top (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) (u : Γ(Y, ⊤)) :
    _root_.GlobalTheory.SS.WtRat.ev g ⊤ h u =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (g.appTop.hom u) := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  rfl

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in

theorem _root_.GlobalTheory.SS.WtRat.ev_spMap (σ : R →+* R') (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (h' : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ ≫ g) ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ ≫ g) V h' u =
      σ (_root_.GlobalTheory.SS.WtRat.ev g V h u) := by
  rw [← _root_.GlobalTheory.SS.WtRat.ev_appLE (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) g V ⊤ h le_top h' u]
  erw [_root_.GlobalTheory.SS.WtRat.ev_top]
  exact congrArg (fun f => CommRingCat.Hom.hom f ((g.appLE V ⊤ h).hom u))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in
private theorem isUnit_of_basicOpen_covers_scheme (X : Scheme) (s : Γ(X, ⊤))
    (hb : ⊤ ≤ X.basicOpen s) : IsUnit s := by
  have := (RingedSpace.isUnit_res_basicOpen _ s).map
    (ConcreteCategory.hom (X.presheaf.map (homOfLE hb).op))
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
  erw [Subsingleton.elim (_ ≫ _) (𝟙 (Opposite.op (⊤ : X.Opens))),
    CategoryTheory.Functor.map_id] at this
  simpa using this

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in

theorem _root_.GlobalTheory.SS.WtRat.isUnit_ev (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (u : Γ(Y, V)) (hu : ⊤ ≤ g ⁻¹ᵁ Y.basicOpen u) :
    IsUnit (_root_.GlobalTheory.SS.WtRat.ev g V h u) := by
  have hb : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R).basicOpen ((g.appLE V ⊤ h).hom u) := by
    have := Scheme.basicOpen_appLE g ⊤ V h u
    erw [this]
    exact le_inf le_rfl hu
  exact (isUnit_of_basicOpen_covers_scheme _ _ hb).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom

end GlobalTheory.SS.WtRat
end
