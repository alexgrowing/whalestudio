import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.HodgeBC_map
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace UpperTheory.Gal.G3.HN

open PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

section Comp

variable {k k' : Type} [CommRing k] [CommRing k'] {φ : k →+* k'}

theorem formPullS_formPull {X Y Y' : Scheme.{0}} {s : X ⟶ Sp k} {r : Y ⟶ Sp k} {r' : Y' ⟶ Sp k'}
    {f : Y ⟶ X} {e : Y' ⟶ Y} (hf : f ≫ s = r) (he : e ≫ r = r' ≫ spMap φ)
    (hu : (e ≫ f) ≫ s = r' ≫ spMap φ) (U : X.Opens) (j : ℕ) (x : OmU s U j) :
    formPullS he (f ⁻¹ᵁ U) j (formPull hf U j x) = formPullS hu U j x := by
  unfold formPullS formPull
  refine SemiHom.mOm_mOm _ _ _ (fun b => ?_) x
  simp only [appSecS, appSec, Scheme.Hom.comp_app]
  rfl

theorem formPull_formPullS {X X' Y' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {r' : Y' ⟶ Sp k'}
    {g : X' ⟶ X} {f' : Y' ⟶ X'} (hg : g ≫ s = s' ≫ spMap φ) (hf' : f' ≫ s' = r')
    (hu : (f' ≫ g) ≫ s = r' ≫ spMap φ) (U : X.Opens) (j : ℕ) (x : OmU s U j) :
    formPull hf' (g ⁻¹ᵁ U) j (formPullS hg U j x) = formPullS hu U j x := by
  unfold formPullS formPull
  refine SemiHom.mOm_mOm _ _ _ (fun b => ?_) x
  simp only [appSecS, appSec, Scheme.Hom.comp_app]
  rfl

theorem omegaPullS_comp_left {X Y Y' : Scheme.{0}} {s : X ⟶ Sp k} {r : Y ⟶ Sp k} {r' : Y' ⟶ Sp k'}
    {f : Y ⟶ X} {e : Y' ⟶ Y} (hf : f ≫ s = r) (he : e ≫ r = r' ≫ spMap φ)
    (hu : (e ≫ f) ≫ s = r' ≫ spMap φ) (j : ℕ) :
    omegaPullS hu j = omegaPull hf j ≫ (Scheme.Modules.pushforward f).map (omegaPullS he j) := by
  apply omega_hom_ext
  intro V y
  rw [omegaPullS_toOmega]
  show _ = (ConcreteCategory.hom ((omegaPullS he j).val.app (op (f ⁻¹ᵁ V))))
    ((ConcreteCategory.hom ((omegaPull hf j).val.app (op V))) ((ConcreteCategory.hom ((toOmega s j).app (op V))) y))
  rw [omegaPull_toOmega, omegaPullS_toOmega, formPullS_formPull hf he hu]
  rfl

theorem omegaPullS_comp_right {X X' Y' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {r' : Y' ⟶ Sp k'}
    {g : X' ⟶ X} {f' : Y' ⟶ X'} (hg : g ≫ s = s' ≫ spMap φ) (hf' : f' ≫ s' = r')
    (hu : (f' ≫ g) ≫ s = r' ≫ spMap φ) (j : ℕ) :
    omegaPullS hu j = omegaPullS hg j ≫ (Scheme.Modules.pushforward g).map (omegaPull hf' j) := by
  apply omega_hom_ext
  intro V y
  rw [omegaPullS_toOmega]
  show _ = (ConcreteCategory.hom ((omegaPull hf' j).val.app (op (g ⁻¹ᵁ V))))
    ((ConcreteCategory.hom ((omegaPullS hg j).val.app (op V))) ((ConcreteCategory.hom ((toOmega s j).app (op V))) y))
  rw [omegaPullS_toOmega, omegaPull_toOmega, formPull_formPullS hg hf' hu]
  rfl

theorem hodgePullS_hodgePull {X Y Y' : Scheme.{0}} {s : X ⟶ Sp k} {r : Y ⟶ Sp k} {r' : Y' ⟶ Sp k'}
    {f : Y ⟶ X} {e : Y' ⟶ Y} (hf : f ≫ s = r) (he : e ≫ r = r' ≫ spMap φ)
    (hu : (e ≫ f) ≫ s = r' ≫ spMap φ) (j q : ℕ) (x : hodgeH s j q) :
    hodgePullS he j q (hodgePull hf j q x) = hodgePullS hu j q x := by
  unfold hodgePullS hodgePull
  change (cohOn.toH' _ _ _).symm (SheafPull.pull _ (toAbSheafPush (omegaPullS he j)) _ _
      ((cohOn.toH' _ _ _) ((cohOn.toH' _ _ _).symm (SheafPull.pull _ (toAbSheafPush (omegaPull hf j)) _ _
        ((cohOn.toH' _ _ _) x))))) =
    (cohOn.toH' _ _ _).symm (SheafPull.pull _ (toAbSheafPush (omegaPullS hu j)) _ _ ((cohOn.toH' _ _ _) x))
  rw [AddEquiv.apply_symm_apply]
  congr 1
  refine (SheafPull.pull_pull f.base e.base (toAbSheafPush (omegaPull hf j))
    (toAbSheafPush (omegaPullS he j)) q _ _ _).trans ?_
  rw [omegaPullS_comp_left hf he hu]
  rfl

theorem hodgePull_hodgePullS {X X' Y' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {r' : Y' ⟶ Sp k'}
    {g : X' ⟶ X} {f' : Y' ⟶ X'} (hg : g ≫ s = s' ≫ spMap φ) (hf' : f' ≫ s' = r')
    (hu : (f' ≫ g) ≫ s = r' ≫ spMap φ) (j q : ℕ) (x : hodgeH s j q) :
    hodgePull hf' j q (hodgePullS hg j q x) = hodgePullS hu j q x := by
  unfold hodgePullS hodgePull
  change (cohOn.toH' _ _ _).symm (SheafPull.pull _ (toAbSheafPush (omegaPull hf' j)) _ _
      ((cohOn.toH' _ _ _) ((cohOn.toH' _ _ _).symm (SheafPull.pull _ (toAbSheafPush (omegaPullS hg j)) _ _
        ((cohOn.toH' _ _ _) x))))) =
    (cohOn.toH' _ _ _).symm (SheafPull.pull _ (toAbSheafPush (omegaPullS hu j)) _ _ ((cohOn.toH' _ _ _) x))
  rw [AddEquiv.apply_symm_apply]
  congr 1
  refine (SheafPull.pull_pull g.base f'.base (toAbSheafPush (omegaPullS hg j))
    (toAbSheafPush (omegaPull hf' j)) q _ _ _).trans ?_
  rw [omegaPullS_comp_right hg hf' hu]
  rfl

theorem hodgePullS_congr {X X' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {u v : X' ⟶ X}
    (huv : u = v) (hu : u ≫ s = s' ≫ spMap φ) (hv : v ≫ s = s' ≫ spMap φ) (j q : ℕ)
    (x : hodgeH s j q) : hodgePullS hu j q x = hodgePullS hv j q x := by
  subst huv
  rfl

theorem hodgePullS_nat_pull {X X' Y Y' : Scheme.{0}} {s : X ⟶ Sp k} {s' : X' ⟶ Sp k'} {g : X' ⟶ X}
    (hg : g ≫ s = s' ≫ spMap φ) {r : Y ⟶ Sp k} {r' : Y' ⟶ Sp k'} {e : Y' ⟶ Y}
    (he : e ≫ r = r' ≫ spMap φ) {f : Y ⟶ X} (hf : f ≫ s = r) {f' : Y' ⟶ X'} (hf' : f' ≫ s' = r')
    (w : e ≫ f = f' ≫ g) (a b : ℕ) (x : hodgeH s a b) :
    hodgePullS he a b (hodgePull hf a b x) = hodgePull hf' a b (hodgePullS hg a b x) := by
  have hu1 : (e ≫ f) ≫ s = r' ≫ spMap φ := by rw [Category.assoc, hf, he]
  have hu2 : (f' ≫ g) ≫ s = r' ≫ spMap φ := by rw [← w]; exact hu1
  rw [hodgePullS_hodgePull hf he hu1, hodgePull_hodgePullS hg hf' hu2]
  exact hodgePullS_congr w hu1 hu2 a b x

end Comp

end UpperTheory.Gal.G3.HN

end
