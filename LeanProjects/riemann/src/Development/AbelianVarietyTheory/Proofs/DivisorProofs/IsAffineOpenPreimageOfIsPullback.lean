import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

namespace GlobalTheory

namespace TopForm

open LB

section Ring

variable {k k' A B : Type} [CommRing k] [CommRing k'] [CommRing A] [CommRing B]
  {α : k →+* A} {β : k' →+* B}

def formMapSq (D : ℕ) (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ) :
    Forms α D →ₛₗ[ρ] Forms β D :=
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  { toFun := exteriorPowerMapOver B D (KaehlerDifferential.map k k' A B)
    map_add' := map_add _
    map_smul' := fun a x => by
      rw [map_smul, ← algebraMap_smul B]
      rfl }

variable {D : ℕ}

theorem formMapSq_dForm (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ) (f : Fin D → A) :
    formMapSq D σ ρ h (dForm α f) = dForm β fun i => ρ (f i) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  change exteriorPowerMapOver B D (KaehlerDifferential.map k k' A B)
    (exteriorPower.ιMulti A D _) = _
  rw [exteriorPowerMapOver_ιMulti, dForm_eq]
  simp only [KaehlerDifferential.map_D]
  rfl

theorem IsFreeGen.formMapSq (σ : k →+* k') (ρ : A →+* B) (h : ρ.comp α = β.comp σ)
    (H : IsPushout (CommRingCat.ofHom α) (CommRingCat.ofHom σ) (CommRingCat.ofHom ρ)
      (CommRingCat.ofHom β)) {ω : Forms α D} (hω : IsFreeGen A ω) :
    IsFreeGen B (formMapSq D σ ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  letI := σ.toAlgebra
  letI := (ρ.comp α).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k k' B := IsScalarTower.of_algebraMap_eq' h
  haveI : SMulCommClass k' A B := SMulCommClass.of_commMonoid _ _ _
  haveI : Algebra.IsPushout k k' A B := (CommRingCat.isPushout_iff_isPushout.1 H).symm
  refine hω.of_isBaseChange (isBaseChange_exteriorPower
    (IsBaseChange.of_equiv (KaehlerDifferential.tensorKaehlerEquiv k k' A B) fun x => ?_) D)
  have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) :=
    (KaehlerDifferential.span_range_derivation k A).ge Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul B, map_smul, hx, map_smul, algebraMap_smul]

end Ring

variable {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {Y Y' : Scheme.{0}}
  {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {φ : Y' ⟶ Y} {D : ℕ}

theorem appLE_comp_algX (w : φ ≫ p = p' ≫ spMap σ) {V : Y.Opens} {W : Y'.Opens}
    (h : W ≤ φ ⁻¹ᵁ V) : (φ.appLE V W h).hom.comp (algX p V) = (algX p' W).comp σ := by
  have e₁ : p.appLE ⊤ V le_top ≫ φ.appLE V W h =
      (spMap σ).appLE ⊤ ⊤ le_top ≫ p'.appLE ⊤ W le_top := by
    refine (Scheme.Hom.appLE_comp_appLE φ p ⊤ V W le_top h).trans (Eq.trans ?_
      (Scheme.Hom.appLE_comp_appLE p' (spMap σ) ⊤ ⊤ W le_top le_top).symm)
    simp only [w]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ)
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at e₂
  have e₃ : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V le_top ≫ φ.appLE V W h =
      CommRingCat.ofHom σ ≫ (Scheme.ΓSpecIso (CommRingCat.of k')).inv ≫ p'.appLE ⊤ W le_top := by
    rw [e₁, ← Category.assoc, ← Category.assoc, e₂]
    rfl
  exact congrArg CommRingCat.Hom.hom e₃

def pullForm (w : φ ≫ p = p' ≫ spMap σ) {V : Y.Opens} {W : Y'.Opens} (h : W ≤ φ ⁻¹ᵁ V) :
    FormsOn p D V →ₛₗ[(φ.appLE V W h).hom] FormsOn p' D W :=
  formMapSq D σ (φ.appLE V W h).hom (appLE_comp_algX w h)

variable (w : φ ≫ p = p' ≫ spMap σ) {U V : Y.Opens} {U' W W' : Y'.Opens}

theorem pullForm_dOn (h : W ≤ φ ⁻¹ᵁ V) (f : Fin D → Γ(Y, V)) :
    pullForm w h (dOn p f) = dOn p' fun a => (φ.appLE V W h).hom (f a) :=
  formMapSq_dForm _ _ _ f

theorem resForm_pullForm (h : W ≤ φ ⁻¹ᵁ V) (e : W' ≤ W) (η : FormsOn p D V) :
    resForm e (pullForm w h η) = pullForm w (e.trans h) η := by
  haveI : RingHomCompTriple (φ.appLE V W h).hom (resG Y' e) (φ.appLE V W' (e.trans h)).hom :=
    ⟨RingHom.ext (resG_appLE φ h e)⟩
  refine LinearMap.congr_fun (forms_ext (φ := (resForm e).comp (pullForm w h))
    (ψ := pullForm w (e.trans h)) fun f => ?_) η
  rw [LinearMap.comp_apply, pullForm_dOn, pullForm_dOn, resForm_dOn]
  simp only [resG_appLE]

theorem pullForm_resForm (e : V ≤ U) (h : W ≤ φ ⁻¹ᵁ V) (η : FormsOn p D U) :
    pullForm w h (resForm e η) = pullForm w (h.trans (φ.preimage_mono e)) η := by
  haveI : RingHomCompTriple (resG Y e) (φ.appLE V W h).hom
      (φ.appLE U W (h.trans (φ.preimage_mono e))).hom :=
    ⟨RingHom.ext (appLE_resG φ e h)⟩
  refine LinearMap.congr_fun (forms_ext (φ := (pullForm w h).comp (resForm e))
    (ψ := pullForm w (h.trans (φ.preimage_mono e))) fun f => ?_) η
  rw [LinearMap.comp_apply, resForm_dOn, pullForm_dOn, pullForm_dOn]
  simp only [appLE_resG]

theorem IsFrame.coeff_pullForm {ω : FormsOn p D U} (hω : IsFrame ω) (hU : U' ≤ φ ⁻¹ᵁ U)
    (hω' : IsFrame (pullForm w hU ω)) (e : V ≤ U) (e' : W ≤ U') (h : W ≤ φ ⁻¹ᵁ V)
    (η : FormsOn p D V) :
    hω'.coeff e' (pullForm w h η) = (φ.appLE V W h).hom (hω.coeff e η) := by
  refine fun_ext_of_cover (fun T : {T : Y.Opens // IsAffineOpen T ∧ T ≤ V} => W ⊓ φ ⁻¹ᵁ T.1)
    (fun _ => inf_le_left) (fun x hx => ?_) fun T => ?_
  · obtain ⟨T, hT⟩ := Opens.mem_iSup.1 (le_iSup_affine V (h hx))
    exact Opens.mem_iSup.2 ⟨T, hx, hT⟩
  · have h₁ := congrArg (pullForm w (inf_le_right : W ⊓ φ ⁻¹ᵁ T.1 ≤ _))
      (hω.resForm_eq_coeff_smul e η T.2.1 T.2.2)
    rw [map_smulₛₗ, pullForm_resForm, pullForm_resForm, appLE_resG] at h₁
    rw [IsFrame.resG_coeff, resForm_pullForm, resG_appLE]
    exact hω'.coeff_eq_of_eq_smul _ (h₁.trans (by rw [resForm_pullForm]))

theorem isAffineOpen_preimage_of_isPullback (H : IsPullback φ p' p (spMap σ))
    (hU : IsAffineOpen U) : IsAffineOpen (φ ⁻¹ᵁ U) :=
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  hU.preimage φ

theorem IsFrame.pullForm (H : IsPullback φ p' p (spMap σ)) {ω : FormsOn p D U} (hω : IsFrame ω)
    (hW : IsAffineOpen W) (h : W ≤ φ ⁻¹ᵁ U) : IsFrame (pullForm H.w h ω) := by
  letI := σ.toAlgebra
  have h₁ : IsFrame (TopForm.pullForm H.w (inf_le_left : φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ ≤ _) ω) := by
    refine ⟨?_, hω.gen.formMapSq σ _ _ (isPushout_sections p p' φ H U hω.affine)⟩
    rw [show φ ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ = φ ⁻¹ᵁ U from inf_top_eq _]
    exact isAffineOpen_preimage_of_isPullback H hω.affine
  have h₂ := h₁.res hW (le_inf h le_top)
  rwa [resForm_pullForm] at h₂

end TopForm

namespace CanonLB

open TopForm LB

variable {k k' : Type} [CommRing k] [CommRing k'] {σ : k →+* k'} {Y Y' : Scheme.{0}}
  {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'} {φ : Y' ⟶ Y} {D : ℕ}
  [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']

theorem isFrame_pull (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D)
    (i : (K.bundle.pull φ).ι) : IsFrame (pullForm H.w (pull_U_le φ i) (K.om (i PUnit.unit))) :=
  (K.isFrame _).pullForm H
    (by rw [pull_U]; exact isAffineOpen_preimage_of_isPullback H (K.affine _)) _

def baseChange (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D) : CanonLB p' D where
  bundle := K.bundle.pull φ
  isLB := Semi.LB.isLB_linComb K.isLB _ _
  affine i := (K.isFrame_pull H i).affine
  om i := pullForm H.w (pull_U_le φ i) (K.om (i PUnit.unit))
  gen i := (K.isFrame_pull H i).gen
  trans i j W hW hi hj := by
    have h : W ≤ φ ⁻¹ᵁ (K.bundle.U (i PUnit.unit) ⊓ K.bundle.U (j PUnit.unit)) :=
      le_inf (hi.trans (pull_U_le φ i)) (hj.trans (pull_U_le φ j))
    have h₁ := (K.isFrame _).coeff_pullForm H.w _ (K.isFrame_pull H i) inf_le_left hi h
      (resForm inf_le_right (K.om (j PUnit.unit)))
    rw [pullForm_resForm] at h₁
    rw [resG_pull_g, g_eq_ratio, resForm_pullForm]
    exact ((K.isFrame_pull H i).coeff_smul_resForm hW hi _).symm.trans (congrArg (· • _) h₁)

theorem jacobian_baseChange (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D)
    (i : (K.bundle.pull φ).ι) {V : Y.Opens} (hV : V ≤ K.bundle.U (i PUnit.unit)) {W : Y'.Opens}
    (hW : W ≤ (K.bundle.pull φ).U i) (h : W ≤ φ ⁻¹ᵁ V) (f : Fin D → Γ(Y, V)) :
    (K.baseChange H).jacobian i hW (fun a => (φ.appLE V W h).hom (f a)) =
      (φ.appLE V W h).hom (K.jacobian (i PUnit.unit) hV f) := by
  have h₁ := (K.isFrame _).coeff_pullForm H.w _ (K.isFrame_pull H i) hV hW h (dOn p f)
  rw [pullForm_dOn] at h₁
  exact h₁

end CanonLB

theorem canonLB_baseChange (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k')
    (Y Y' : Scheme.{0}) (p : Y ⟶ Sp k) (p' : Y' ⟶ Sp k') (φ : Y' ⟶ Y) (D : ℕ)
    [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']
    (H : IsPullback φ p' p (spMap σ)) (K : CanonLB p D) (K' : CanonLB p' D) :
    ∃ w : LB.Iso K'.bundle (K.bundle.pull φ), w.IsGen ∧
      ∀ (i : (K.bundle.pull φ).ι) (j : K'.bundle.ι) (V : Y.Opens)
        (hV : V ≤ K.bundle.U (i PUnit.unit)) (W : Y'.Opens) (hW : W ≤ K'.bundle.U j)
        (h : W ≤ φ ⁻¹ᵁ V) (hw : W ≤ (LB.div (K.bundle.pull φ) K'.bundle).U (i, j))
        (f : Fin D → Γ(Y, V)),
        (φ.appLE V W h).hom (K.jacobian (i PUnit.unit) hV f) =
          resG Y' hw (w.s (i, j)).val * K'.jacobian j hW (fun a => (φ.appLE V W h).hom (f a)) :=
  ⟨K'.iso (K.baseChange H), K'.iso_isGen (K.baseChange H), fun i j _ hV _ hW h hw f =>
    (K.jacobian_baseChange H i hV (hw.trans inf_le_left) h f).symm.trans
      (K'.coeff_eq_iso_mul (K.baseChange H) i j _ hW _)⟩

end GlobalTheory
