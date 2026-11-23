import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

variable {k k' : Type} [CommRing k] [CommRing k'] {φ : k →+* k'} {X X' : Scheme.{0}}
  {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {g : X' ⟶ X}

theorem algΓ_comp_spMap (t : X' ⟶ Sp k') (r : k) :
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (t ≫ spMap φ).appTop).hom r =
      ((Scheme.ΓSpecIso (CommRingCat.of k')).inv ≫ t.appTop).hom (φ r) := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem secMap_comp_spMap (t : X' ⟶ Sp k') (W : X'.Opens) (r : k) :
    (secMap (t ≫ spMap φ) W).hom r = (secMap t W).hom (φ r) := by
  change (X'.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (t ≫ spMap φ).appTop).hom r) =
    (X'.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
      (((Scheme.ΓSpecIso (CommRingCat.of k')).inv ≫ t.appTop).hom (φ r))
  rw [algΓ_comp_spMap]

variable (s s' g) in

def appSecS (U : X.Opens) : Sec s U →+* Sec s' (g ⁻¹ᵁ U) := (g.app U).hom

theorem semiHom_appSecS (hg : g ≫ s = s' ≫ spMap φ) (U : X.Opens) :
    SemiHom φ (appSecS s s' g U) := fun r b ↦ by
  refine (semiHom_appSec (s' := s' ≫ spMap φ) hg U r b).trans ?_
  change (secMap (s' ≫ spMap φ) (g ⁻¹ᵁ U)).hom r * (g.app U).hom b =
    (secMap s' (g ⁻¹ᵁ U)).hom (φ r) * (g.app U).hom b
  rw [secMap_comp_spMap]

theorem appTop_algebraMapS (hg : g ≫ s = s' ≫ spMap φ) (r : k) :
    letI := algΓ s; letI := algΓ s'
    g.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k' Γ(X', ⊤) (φ r) :=
  (appTop_algebraMap (s' := s' ≫ spMap φ) hg r).trans (algΓ_comp_spMap s' r)

def formPullS (hg : g ≫ s = s' ≫ spMap φ) (U : X.Opens) (j : ℕ) :
    OmU s U j →ₛₗ[φ] OmU s' (g ⁻¹ᵁ U) j :=
  (semiHom_appSecS hg U).mOm j

theorem formPullS_smul (hg : g ≫ s = s' ≫ spMap φ) (U : X.Opens) {j : ℕ} (b : Sec s U)
    (x : OmU s U j) : formPullS hg U j (b • x) = appSecS s s' g U b • formPullS hg U j x :=
  SemiHom.mOm_smul _ b x

theorem formRes_formPullS (hg : g ≫ s = s' ≫ spMap φ) {U V : X.Opens} (h : V ≤ U) {j : ℕ}
    (x : OmU s U j) :
    formRes s' (g.preimage_mono h) j (formPullS hg U j x) = formPullS hg V j (formRes s h j x) := by
  have e : ∀ b : Sec s U, Sec.res s' (g.preimage_mono h) (appSecS s s' g U b) =
      appSecS s s' g V (Sec.res s h b) := fun b ↦ by
    change (g.app U ≫ X'.presheaf.map (homOfLE (g.preimage_mono h)).op).hom b =
      (X.presheaf.map (homOfLE h).op ≫ g.app V).hom b
    rw [g.naturality]; rfl
  have hγ : SemiHom φ ((appSecS s s' g V).comp (Sec.res s h : Sec s U →+* Sec s V)) :=
    (SemiHom.of_algHom (Sec.res s h)).comp (semiHom_appSecS hg V)
  exact (SemiHom.mOm_mOm (semiHom_appSecS hg U) (SemiHom.of_algHom (Sec.res s' (g.preimage_mono h)))
    hγ e x).trans (SemiHom.mOm_mOm (SemiHom.of_algHom (Sec.res s h)) (semiHom_appSecS hg V) hγ
      (fun _ ↦ rfl) x).symm

def pullPreS (hg : g ≫ s = s' ≫ spMap φ) (j : ℕ) : formsPre s j ⟶
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
      ((Scheme.Modules.pushforward g).obj (Omega s' j)) where
  app U := ModuleCat.ofHom
    { toFun x := ((toOmega s' j).app (op (g ⁻¹ᵁ U.unop))).hom (formPullS hg U.unop j x)
      map_add' x y := (congrArg _ (map_add _ x y)).trans (map_add _ _ _)
      map_smul' b x := (congrArg ((toOmega s' j).app (op (g ⁻¹ᵁ U.unop))).hom
        (formPullS_smul hg U.unop b x)).trans
          (((toOmega s' j).app (op (g ⁻¹ᵁ U.unop))).hom.map_smul (appSecS s s' g U.unop b) _) }
  naturality {U V} i := by
    ext x
    exact (congrArg ((toOmega s' j).app (op (g ⁻¹ᵁ V.unop))).hom
      (formRes_formPullS hg (leOfHom i.unop) x)).symm.trans
        (PresheafOfModules.naturality_apply (toOmega s' j)
          ((TopologicalSpace.Opens.map g.base).map i.unop).op (formPullS hg U.unop j x))

def omegaPullS (hg : g ≫ s = s' ≫ spMap φ) (j : ℕ) :
    Omega s j ⟶ (Scheme.Modules.pushforward g).obj (Omega s' j) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm
    (pullPreS hg j)

theorem omegaPullS_toOmega (hg : g ≫ s = s' ≫ spMap φ) (j : ℕ) (U : X.Opens) (x : OmU s U j) :
    (omegaPullS hg j).val.app (op U) ((toOmega s j).app (op U) x) =
      (toOmega s' j).app (op (g ⁻¹ᵁ U)) (formPullS hg U j x) := by
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
    (formsPre s j) ((Scheme.Modules.pushforward g).obj (Omega s' j)) (omegaPullS hg j)
  rw [omegaPullS, Equiv.apply_symm_apply] at h
  have h2 := congrArg (fun ψ ↦ (ψ.app (op U)).hom x) h
  exact h2.symm

def hodgePullS (hg : g ≫ s = s' ≫ spMap φ) (j q : ℕ) : hodgeH s j q →ₛₗ[φ] hodgeH s' j q :=
  letI := algΓ s; letI := algΓ s'
  cohOn.pull (appTop_algebraMapS hg) (omegaPullS hg j) (le_refl (g ⁻¹ᵁ ⊤)) q

example (hg : g ≫ s = s' ≫ spMap φ) (x : hodgeH s 1 1) (r : k) :
    hodgePullS hg 1 1 (r • x) = φ r • hodgePullS hg 1 1 x :=
  map_smulₛₗ _ r x

end PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

end
