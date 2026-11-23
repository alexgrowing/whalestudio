import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsPullbackFaithful
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency.types false in

theorem pullback_map_injective_unit {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A : U.Modules}
    (φ₁ φ₂ : A ⟶ structureModule U)
    (h : (Scheme.Modules.pullback g).map φ₁ = (Scheme.Modules.pullback g).map φ₂) : φ₁ = φ₂ := by
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  have key : ∀ φ : A ⟶ structureModule U,
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _)
        ((Scheme.Modules.pullback g).map φ ≫
          SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) =
      φ ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
    intro φ
    rw [Adjunction.homEquiv_naturality_left]
    congr 1
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have h2 : φ₁ ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom =
      φ₂ ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
    rw [← key, ← key, h]
  ext W x
  have := congr((($h2).app W).hom x)
  exact hg W this

section Coordinates

variable {X : Scheme.{u}} {B : X.Modules} {n : ℕ} {s : Fin n → Γ(B, ⊤)}

variable (B s) in

def basisExpand (W : X.Opens) : (Fin n → Γ(X, W)) →ₗ[Γ(X, W)] Γ(B, W) :=
  Fintype.linearCombination Γ(X, W)
    (fun i => (B.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom (s i))

lemma basisExpand_apply (W : X.Opens) (r : Fin n → Γ(X, W)) :
    basisExpand B s W r = ∑ i, r i • (B.presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom (s i) :=
  Fintype.linearCombination_apply _ _ _

lemma basisExpand_map {W W' : X.Opens} (i : W' ≤ W) (r : Fin n → Γ(X, W)) :
    (B.presheaf.map (homOfLE i).op).hom (basisExpand B s W r) =
      basisExpand B s W' (fun k => (X.presheaf.map (homOfLE i).op).hom (r k)) := by
  rw [basisExpand_apply, basisExpand_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Scheme.Modules.map_smul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

def basisEquiv (hs : IsBasisOn B ⊤ s) (W : X.Opens) :
    (Fin n → Γ(X, W)) ≃ₗ[Γ(X, W)] Γ(B, W) :=
  LinearEquiv.ofBijective (basisExpand B s W) (by
    have := hs W le_top
    convert this using 1
    funext r
    exact basisExpand_apply W r)

lemma basisEquiv_symm_map (hs : IsBasisOn B ⊤ s) {W W' : X.Opens} (i : W' ≤ W) (x : Γ(B, W))
    (k : Fin n) :
    (basisEquiv hs W').symm ((B.presheaf.map (homOfLE i).op).hom x) k =
      (X.presheaf.map (homOfLE i).op).hom ((basisEquiv hs W).symm x k) := by
  obtain ⟨r, rfl⟩ := (basisEquiv hs W).surjective x
  rw [LinearEquiv.symm_apply_apply]
  have : (B.presheaf.map (homOfLE i).op).hom (basisEquiv hs W r) =
      basisEquiv hs W' (fun k => (X.presheaf.map (homOfLE i).op).hom (r k)) :=
    basisExpand_map i r
  rw [this, LinearEquiv.symm_apply_apply]

def basisCoord (hs : IsBasisOn B ⊤ s) (j : Fin n) : B ⟶ structureModule X :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom
        ((LinearMap.proj j ∘ₗ (basisEquiv hs W.unop).symm.toLinearMap).toAddMonoidHom)
      naturality := fun W W' f => by
        ext x
        exact basisEquiv_symm_map hs (leOfHom f.unop) x j }
    (fun W r x =>
      (LinearMap.proj j ∘ₗ (basisEquiv hs W.unop).symm.toLinearMap).map_smul r x)⟩

theorem eq_of_basisCoord (hs : IsBasisOn B ⊤ s) {A : X.Modules} (ψ₁ ψ₂ : A ⟶ B)
    (h : ∀ j, ψ₁ ≫ basisCoord hs j = ψ₂ ≫ basisCoord hs j) : ψ₁ = ψ₂ := by
  ext W x
  apply (basisEquiv hs W).symm.injective
  funext j
  exact congr((($(h j)).app W).hom x)

end Coordinates

theorem pullback_faithful_of_basis {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A B : U.Modules} {n : ℕ}
    {s : Fin n → Γ(B, ⊤)} (hs : IsBasisOn B ⊤ s) (ψ₁ ψ₂ : A ⟶ B)
    (h : (Scheme.Modules.pullback g).map ψ₁ = (Scheme.Modules.pullback g).map ψ₂) : ψ₁ = ψ₂ :=
  eq_of_basisCoord hs ψ₁ ψ₂ fun j => pullback_map_injective_unit g hg _ _
    (by rw [Functor.map_comp, Functor.map_comp, h])

set_option backward.isDefEq.respectTransparency.types false in

theorem restrict_map_eq_of_pullback {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A B : U.Modules} (V : U.Opens) {n : ℕ}
    {s : Fin n → Γ(B, V)} (hs : IsBasisOn B V s) (ψ₁ ψ₂ : A ⟶ B)
    (h : (Scheme.Modules.pullback g).map ψ₁ = (Scheme.Modules.pullback g).map ψ₂) :
    (Scheme.Modules.restrictFunctor V.ι).map ψ₁ = (Scheme.Modules.restrictFunctor V.ι).map ψ₂ := by
  have hs' := (hs.restrict V.ι_image_top.le).restrictImage V.ι
  have hg' : ∀ W, Function.Injective ((g ∣_ V).app W) := by
    intro W
    rw [morphismRestrict_app]
    exact (ConcreteCategory.bijective_of_isIso
      (T.presheaf.map (eqToHom (image_morphismRestrict_preimage g V W)).op)).1.comp (hg _)
  let E : Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback (g ∣_ V) ≅
      Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback (g ⁻¹ᵁ V).ι :=
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι) _ ≪≫
      Scheme.Modules.pullbackComp _ _ ≪≫
        Scheme.Modules.pullbackCongr (morphismRestrict_ι g V) ≪≫
          (Scheme.Modules.pullbackComp _ _).symm
  apply pullback_faithful_of_basis (g ∣_ V) hg' hs'
  refine (NatIso.naturality_2 E ψ₁).symm.trans (Eq.trans ?_ (NatIso.naturality_2 E ψ₂))
  simp only [Functor.comp_map, h]

theorem PullbackFaithful.proof : PullbackFaithful.Statement := by
  intro T U g hg A B hB ψ₁ ψ₂ h
  choose V hVa hxV n s hs using hB
  have loc : ∀ x : U, (Scheme.Modules.restrictFunctor (V x).ι).map ψ₁ =
      (Scheme.Modules.restrictFunctor (V x).ι).map ψ₂ :=
    fun x => restrict_map_eq_of_pullback g hg (V x) (hs x) ψ₁ ψ₂ h
  ext W a
  let F : TopCat.Sheaf Ab U := ⟨B.presheaf, B.isSheaf⟩
  refine F.eq_of_locally_eq' (fun x : W => (V x).ι ''ᵁ ((V x).ι ⁻¹ᵁ W)) W
    (fun x => homOfLE ((V x.1).ι.image_preimage_le W)) ?_ _ _ fun x => ?_
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, ⟨y, hxV y⟩, hy, rfl⟩
  · change (B.presheaf.map _).hom ((ψ₁.app W).hom a) = (B.presheaf.map _).hom ((ψ₂.app W).hom a)
    rw [← app_map_apply, ← app_map_apply]
    exact congr((($(loc x.1)).app ((V x.1).ι ⁻¹ᵁ W)).hom _)

end

end GroundTheory.Heights₂.Heights.Model
