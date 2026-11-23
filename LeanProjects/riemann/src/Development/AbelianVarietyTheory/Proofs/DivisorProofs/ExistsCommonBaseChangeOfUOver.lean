import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem exists_common_baseChange_of_uOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (K R R' : Type) [Field K] [CommRing R] [CommRing R'] (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (σ : R →+* K) (σ' : R' →+* K) (u : Sp K ⟶ Xo.XF cf), UOver Xo cf P σ u → UOver Xo cf P' σ' u → ∃ (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsGrpPullback P₀.A P.A (spMap σ) a ∧ IsGrpPullback P₀.A P'.A (spMap σ') a' ∧ LBIso P₀.L (P.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') := by
  intro E _ _ _ H Dw l Xo cf K R R' _ _ _ P P' σ σ' u h h'
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  obtain ⟨G', _, α', β', hα', hβ', hL'⟩ := h'
  obtain ⟨P₀, φ, hφ, hLφ⟩ := exists_pol_baseChange P (spMap σ)
  obtain ⟨e₀, _, he₀⟩ := grpPullback_iso hφ hα
  obtain ⟨e, _, he⟩ := grpPullback_iso hβ hβ'
  haveI : IsMonHom (e₀ ≪≫ e).hom := inferInstanceAs (IsMonHom (e₀.hom ≫ e.hom))
  have hU := Xo.univ.t.PP.isLB
  have X1 : LBIso (P.L.pull φ) (Xo.univ.t.PP.L.pull (e₀.hom.left ≫ β)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp e₀.hom.left he₀.symm rfl hL
  have X2 : LBIso (Xo.univ.t.PP.L.pull (e₀.hom.left ≫ β)) (P'.L.pull ((e₀.hom.left ≫ e.hom.left) ≫ α')) :=
    GlobalTheory.GenSpread.lbIso_pull_comp (e₀.hom.left ≫ e.hom.left) (by rw [← he, Category.assoc]) rfl hL'.symm
  refine ⟨P₀, φ, (e₀.hom.left ≫ e.hom.left) ≫ α', hφ,
    ((isGrpPullback_of_iso (e₀ ≪≫ e)).comp hα').congr (Category.id_comp _) rfl, hLφ,
    LBIso.trans P₀.isLB (pull_isLB P.isLB _) (pull_isLB P'.isLB _) hLφ
      (LBIso.trans (pull_isLB P.isLB _) (pull_isLB hU _) (pull_isLB P'.isLB _) X1 X2)⟩

end GlobalTheory.UPoinc
