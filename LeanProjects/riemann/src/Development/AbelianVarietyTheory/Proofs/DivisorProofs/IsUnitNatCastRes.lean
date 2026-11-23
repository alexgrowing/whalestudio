import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.UnitGlue

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

def Xp (X : Scheme.{0}) (p : ℕ) : X.Opens := X.basicOpen (p : Γ(X, ⊤))

variable {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} {Xw : X.Opens} {K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]}
  (h : ∀ x : X, UnitChartAt p Xw K x)

def cR (x : X) : Type := Classical.choose (h x)

instance instCommRingCR (x : X) : CommRing (cR h x) := Classical.choose (Classical.choose_spec (h x))

def cξ (x : X) : Sp (cR h x) ⟶ X := Classical.choose (Classical.choose_spec (Classical.choose_spec (h x)))

def cu (x : X) : (Localization.Away (p : cR h x))ˣ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (h x))))

theorem c_spec (x : X) : IsOpenImmersion (cξ h x) ∧ x ∈ Set.range (cξ h x) ∧
    ∀ φ : cR h x →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ cξ h x) →
      ∀ ψ : Localization.Away (p : cR h x) →+* ℂ_[p], ψ.comp (algebraMap (cR h x) _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
        ∀ κ ∈ K (spMap φ ≫ cξ h x), ‖ψ (cu h x : Localization.Away (p : cR h x)) - κ‖ < ‖κ‖ :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (h x))))

instance instOpenImmCξ (x : X) : IsOpenImmersion (cξ h x) := (c_spec h x).1

def Uc (x : X) : X.Opens := cξ h x ''ᵁ ⊤

def secMap (x : X) : cR h x →+* Γ(X, Uc h x) :=
  ((cξ h x).appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (cR h x))).inv.hom

theorem isUnit_natCast_res (x : X) :
    IsUnit ((X.presheaf.map (homOfLE (inf_le_left : Uc h x ⊓ Xp X p ≤ Uc h x)).op).hom.comp (secMap h x) (p : cR h x)) := by
  rw [map_natCast]
  have h1 := (X.toRingedSpace.isUnit_res_basicOpen (p : Γ(X, ⊤))).map
    (X.presheaf.map (homOfLE (inf_le_right : Uc h x ⊓ Xp X p ≤ Xp X p)).op).hom
  simp only [map_natCast] at h1
  erw [map_natCast] at h1
  exact h1

def ev (x : X) : Localization.Away (p : cR h x) →+* Γ(X, Uc h x ⊓ Xp X p) :=
  IsLocalization.Away.lift (p : cR h x) (isUnit_natCast_res h x)

def Cx (x : X) : Γ(X, Uc h x ⊓ Xp X p)ˣ := Units.map (ev h x).toMonoidHom (cu h x)

def RatioProp (x y : X) (u : Γ(X, Uc h x ⊓ Uc h y)ˣ) : Prop :=
  res (inf_le_left : Uc h x ⊓ Uc h y ⊓ Xp X p ≤ Uc h x ⊓ Uc h y) u *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : Uc h x ⊓ Uc h y ⊓ Xp X p ≤ Uc h y ⊓ Xp X p) (Cx h y) =
    res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : Uc h x ⊓ Uc h y ⊓ Xp X p ≤ Uc h x ⊓ Xp X p) (Cx h x) ∧
  ((u : Γ(X, Uc h x ⊓ Uc h y)) - 1) ∈ (Ideal.span {(p : Γ(X, Uc h x ⊓ Uc h y))}).radical

open Classical in

def gU (x y : X) : Γ(X, Uc h x ⊓ Uc h y)ˣ :=
  if hh : ∃ u, RatioProp h x y u then hh.choose else 1

def glueLB : LB X := ⟨X, Uc h, gU h⟩

open Classical in

def sigGen {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (f : X ⟶ Spec (.of O)) :
    ((glueLB h).pull (genericι f)).Gen where
  s := fun j =>
    if hh : LB.wchart (glueLB h) (fun _ : PUnit => genericι f) j ≤ genericι f ⁻¹ᵁ (Uc h (j PUnit.unit) ⊓ Xp X p) then
      res hh (pullU (genericι f) _ (Cx h (j PUnit.unit)))
    else 1

end GlobalTheory.UnitGlue
