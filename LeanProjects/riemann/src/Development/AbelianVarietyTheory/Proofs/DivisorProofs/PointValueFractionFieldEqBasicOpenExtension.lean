import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecAppLETopEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

theorem valR_cst_eq_iota : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R) (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* FractionRing Ω), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = algebraMap Ω (FractionRing Ω) (φ r)) → ∀ (O : G.left.Opens) (h : O ≤ G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ O → ∀ θ, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') O (GlobalTheory.HeatV.cst G.hom _ h θ) = iota θ := by
  intro R _ G Ω _ _ φ x' hx c iota hiota O h hO θ
  rw [GlobalTheory.CechKSSmul.valR_appLE_comp _ G.hom (GlobalTheory.HeatV.bo R c).1 O h hO θ]
  have hz : (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ)) := by
    rw [Category.assoc, hx]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have h' : ⊤ ≤ ((spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom) ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 :=
    fun p hp => h (hO hp)
  set s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c with hs
  set z := (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom with hzdef
  let F : Γ(Sp R, (Sp R).basicOpen s) →+* FractionRing Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom.comp (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom
  have hF : ∀ θ, valR z (GlobalTheory.HeatV.bo R c).1 θ = F θ := fun θ => by
    simp only [valR, dif_pos h']; rfl
  suffices e : F = iota by rw [hF]; exact DFunLike.congr_fun e θ
  refine IsLocalization.ringHom_ext (Submonoid.powers s) (S := Γ(Sp R, (Sp R).basicOpen s)) ?_
  ext y0
  obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r = y0 :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y0, by simp⟩
  have e1 : algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      GlobalTheory.HeatV.resV R c r := rfl
  change F (GlobalTheory.HeatV.resV R c r) = iota (GlobalTheory.HeatV.resV R c r)
  rw [hiota]
  show (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom
    ((z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom (GlobalTheory.HeatV.resV R c r)) = _
  have e2 : (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op ≫ z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h' =
      z.appTop := by
    exact (Scheme.Hom.map_appLE z h' _).trans (Scheme.Hom.appLE_eq_app z)
  have e3 : (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom
      (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      z.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [← e2]; rfl
  rw [show (GlobalTheory.HeatV.resV R c r) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) from rfl, e3]
  rw [hz]
  have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  rw [n]
  simp

end GlobalTheory.HeatV
