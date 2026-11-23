import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Annihilator
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

lemma finite_of_semilinear {R R' M M' : Type*} [CommRing R] [CommRing R'] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R' M'] (σ : R →+* R') (hσ : Function.Surjective σ)
    (e : M ≃+ M') (he : ∀ (r : R) (m : M), e (r • m) = σ r • e m) [Module.Finite R' M'] :
    Module.Finite R M := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R') (M := M')
  refine ⟨⟨s.image e.symm, ?_⟩⟩
  rw [eq_top_iff]
  intro m _
  have key : ∀ x ∈ Submodule.span R' (s : Set M'),
      e.symm x ∈ Submodule.span R ((s.image e.symm : Finset M) : Set M) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r' y _ hy =>
      obtain ⟨r, rfl⟩ := hσ r'
      have : e.symm (σ r • y) = r • e.symm y := by
        apply e.injective
        rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      rw [this]
      exact Submodule.smul_mem _ _ hy
  simpa using key (e m) (hs ▸ Submodule.mem_top)

section Affine

variable {T U : Scheme.{u}}

theorem isQuasicoherent_pullback_of_isAffine (g : T ⟶ U) [IsAffine T] [IsAffine U]
    (N : U.Modules) [N.IsQuasicoherent] : ((Scheme.Modules.pullback g).obj N).IsQuasicoherent := by
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = T.isoSpec.inv ≫ g ≫ U.isoSpec.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hg : g = T.isoSpec.hom ≫ Spec.map φ ≫ U.isoSpec.inv := by simp [hφ]
  rw [hg]
  let N₁ := (Scheme.Modules.pullback U.isoSpec.inv).obj N
  have : N₁.IsQuasicoherent := Etale.isQuasicoherent_pullback_of_isIso _ N
  have : IsIso N₁.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ N₁).mp inferInstance
  let N₂ := (Scheme.Modules.pullback (Spec.map φ)).obj N₁
  have : N₂.IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ N₂).mpr (Etale.isIso_fromTildeΓ_pullback φ N₁)
  have : ((Scheme.Modules.pullback T.isoSpec.hom).obj N₂).IsQuasicoherent :=
    Etale.isQuasicoherent_pullback_of_isIso _ N₂
  let e : (Scheme.Modules.pullback T.isoSpec.hom).obj N₂ ≅
      (Scheme.Modules.pullback (T.isoSpec.hom ≫ Spec.map φ ≫ U.isoSpec.inv)).obj N :=
    (Scheme.Modules.pullback T.isoSpec.hom).mapIso
        ((Scheme.Modules.pullbackComp (Spec.map φ) U.isoSpec.inv).app N) ≪≫
      (Scheme.Modules.pullbackComp T.isoSpec.hom (Spec.map φ ≫ U.isoSpec.inv)).app N
  exact (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso e inferInstance

theorem finite_pullback_of_isAffine (g : T ⟶ U) [IsAffine T] [IsAffine U] (N : U.Modules)
    [N.IsQuasicoherent] [Module.Finite Γ(U, ⊤) Γ(N, ⊤)] :
    Module.Finite Γ(T, ⊤) Γ((Scheme.Modules.pullback g).obj N, ⊤) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(U, ⊤)) (M := Γ(N, ⊤))
  let P := Γ((Scheme.Modules.pullback g).obj N, ⊤)
  let L : Submodule Γ(T, ⊤) P :=
    Submodule.span Γ(T, ⊤) ((s.image (Etale.pullbackSection g N) : Finset P) : Set P)
  have hmem : ∀ n : Γ(N, ⊤), Etale.pullbackSection g N n ∈ L := by
    intro n
    have hn : n ∈ Submodule.span Γ(U, ⊤) (s : Set Γ(N, ⊤)) := hs ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact L.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact L.add_mem hx hy
    | smul r x _ hx => rw [Etale.pullbackSection_smul]; exact L.smul_mem _ hx
  have hL : L = ⊤ := by
    obtain ⟨ψ', -, huniq⟩ := Etale.existsUnique_pullbackSection g N (P ⧸ L) 0
      (fun a n => by simp)
    have h0 : (0 : P →ₗ[Γ(T, ⊤)] (P ⧸ L)) = ψ' := huniq 0 (fun n => by simp)
    have h1 : L.mkQ = ψ' := huniq L.mkQ (fun n => by
      simpa using (Submodule.Quotient.mk_eq_zero L).2 (hmem n))
    rw [eq_top_iff]
    intro q _
    have := LinearMap.congr_fun (h1.trans h0.symm) q
    exact (Submodule.Quotient.mk_eq_zero L).1 this
  exact ⟨⟨s.image (Etale.pullbackSection g N), hL⟩⟩

end Affine

section Pullback

variable {X Y : Scheme.{u}}

lemma finite_restrict_top (F : X.Modules) (U : X.Opens)
    [Module.Finite Γ(X, U.ι ''ᵁ ⊤) Γ(F, U.ι ''ᵁ ⊤)] :
    Module.Finite Γ(U, ⊤) Γ(F.restrict U.ι, ⊤) := by
  refine finite_of_semilinear (U.ι.appIso ⊤).inv.hom
    (ConcreteCategory.bijective_of_isIso (U.ι.appIso ⊤).inv).2
    (F.restrictAppIso U.ι ⊤).addCommGroupIsoToAddEquiv fun r m => ?_
  have hs := congrArg (fun φ : Γ(F.restrict U.ι, ⊤) ⟶ Γ(F, U.ι ''ᵁ ⊤) => φ m)
    (Scheme.Modules.smul_restrictAppIso_hom U.ι F ⊤ r)
  exact hs

lemma finite_of_finite_restrict_top (F : X.Modules) (U : X.Opens)
    [Module.Finite Γ(U, ⊤) Γ(F.restrict U.ι, ⊤)] :
    Module.Finite Γ(X, U.ι ''ᵁ ⊤) Γ(F, U.ι ''ᵁ ⊤) := by
  refine finite_of_semilinear (U.ι.appIso ⊤).hom.hom
    (ConcreteCategory.bijective_of_isIso (U.ι.appIso ⊤).hom).2
    (F.restrictAppIso U.ι ⊤).addCommGroupIsoToAddEquiv.symm fun r m => ?_
  have hs := congrArg (fun φ : Γ(F, U.ι ''ᵁ ⊤) ⟶ Γ(F.restrict U.ι, ⊤) => φ m)
    (Scheme.Modules.smul_restrictAppIso_inv U.ι F ⊤ r)
  exact hs

lemma isQuasicoherent_restrict_fromSpec (M : Y.Modules) {V : Y.Opens} (hV : IsAffineOpen V)
    (h : (M.restrict V.ι).IsQuasicoherent) : (M.restrict hV.fromSpec).IsQuasicoherent := by
  have : IsAffine V := hV
  let e : (M.restrict V.ι).restrict hV.isoSpec.inv ≅ M.restrict hV.fromSpec :=
    ((Scheme.Modules.restrictFunctorComp hV.isoSpec.inv V.ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hV.isoSpec_inv_ι).app M
  have h2 : ((M.restrict V.ι).restrict hV.isoSpec.inv).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  exact (SheafOfModules.isQuasicoherent (Spec Γ(Y, V)).ringCatSheaf).prop_of_iso e h2

lemma isQuasicoherent_of_restrict_affine (M : Y.Modules) {ι : Type u} (V : ι → Y.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (h : ∀ i, (M.restrict (V i).ι).IsQuasicoherent) : M.IsQuasicoherent :=
  isQuasicoherent_of_restrict M V hcov fun i =>
    nonempty_presentation_restrict M (hV i) (isQuasicoherent_restrict_fromSpec M (hV i) (h i))

def restrictPullbackIso (ψ : Y ⟶ X) (F : X.Modules) (U : X.Opens) (V : Y.Opens)
    (h : V ≤ ψ ⁻¹ᵁ U) :
    ((Scheme.Modules.pullback ψ).obj F).restrict V.ι ≅
      (Scheme.Modules.pullback (ψ.resLE U V h)).obj (F.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp V.ι ψ).app F ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι ψ h).symm).app F ≪≫
    ((Scheme.Modules.pullbackComp (ψ.resLE U V h) U.ι).app F).symm ≪≫
    (Scheme.Modules.pullback (ψ.resLE U V h)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm

lemma finite_of_iso_app {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (W : Z.Opens)
    [Module.Finite Γ(Z, W) Γ(M, W)] : Module.Finite Γ(Z, W) Γ(N, W) :=
  Module.Finite.equiv
    { toFun := e.hom.app W
      invFun := e.inv.app W
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul e.hom
      left_inv := fun x => by
        rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]; rfl
      right_inv := fun x => by
        rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]; rfl }

theorem isCoherent_pullback (ψ : Y ⟶ X) {F : X.Modules} (hF : IsCoherent F) :
    IsCoherent ((Scheme.Modules.pullback ψ).obj F) := by
  have := hF.1
  let ι := {p : X.affineOpens × Y.affineOpens // p.2.1 ≤ ψ ⁻¹ᵁ p.1.1}
  let Vo : ι → Y.Opens := fun i => i.1.2.1
  have hcov : iSup Vo = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (ψ.base y)) isOpen_univ
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hyV, hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ ψ ⁻¹ᵁ U₀ from hyU)
        (ψ ⁻¹ᵁ U₀).isOpen
    exact Opens.mem_iSup.2 ⟨⟨(⟨U₀, hU₀⟩, ⟨V₀, hV₀⟩), hVU⟩, hyV⟩
  let F' := (Scheme.Modules.pullback ψ).obj F
  have hloc : ∀ i : ι, (F'.restrict (Vo i).ι).IsQuasicoherent ∧
      Module.Finite Γ(Vo i, ⊤) Γ(F'.restrict (Vo i).ι, ⊤) := by
    intro i
    have hU := i.1.1.2
    have hV := i.1.2.2
    have : IsAffine i.1.1.1 := hU
    have : IsAffine i.1.2.1 := hV
    have hfin : Module.Finite Γ(X, i.1.1.1.ι ''ᵁ ⊤) Γ(F, i.1.1.1.ι ''ᵁ ⊤) :=
      hF.2 _ ((isAffineOpen_top _).image_of_isOpenImmersion _)
    have : Module.Finite Γ(i.1.1.1, ⊤) Γ(F.restrict i.1.1.1.ι, ⊤) := finite_restrict_top F _
    let e := restrictPullbackIso ψ F i.1.1.1 i.1.2.1 i.2
    have := isQuasicoherent_pullback_of_isAffine (ψ.resLE _ _ i.2) (F.restrict i.1.1.1.ι)
    have := finite_pullback_of_isAffine (ψ.resLE _ _ i.2) (F.restrict i.1.1.1.ι)
    exact ⟨(SheafOfModules.isQuasicoherent (Vo i).toScheme.ringCatSheaf).prop_of_iso e.symm
      inferInstance, finite_of_iso_app e.symm ⊤⟩
  have : F'.IsQuasicoherent :=
    isQuasicoherent_of_restrict_affine F' Vo (fun i => i.1.2.2) hcov fun i => (hloc i).1
  refine isCoherent_of_affineCover F' (fun i => (Vo i).ι ''ᵁ ⊤)
    (fun i => (isAffineOpen_top _).image_of_isOpenImmersion _) ?_ fun i => ?_
  · simp only [Scheme.Opens.ι_image_top]
    exact hcov
  · have : IsAffine (Vo i) := i.1.2.2
    have := (hloc i).2
    exact finite_of_finite_restrict_top F' (Vo i)

end Pullback

section Support

variable {X : Scheme.{u}}

theorem exists_pushforward_iso_of_supportedIn (F : X.Modules) (hF : IsCoherent F) {T : Set X}
    (hT : IsClosed T) (hFT : Scheme.Modules.SupportedIn F T) :
    ∃ I : X.IdealSheafData, (I.support : Set X) ⊆ T ∧ ∃ G : I.subscheme.Modules, IsCoherent G ∧
      Nonempty ((Scheme.Modules.pushforward I.subschemeι).obj G ≅ F) := by
  have := hF.1
  let I := annihilatorIdealSheaf F hF
  refine ⟨I, support_annihilatorIdealSheaf_subset F hF hT hFT,
    (Scheme.Modules.pullback I.subschemeι).obj F, isCoherent_pullback _ hF, ?_⟩
  let adj := Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι
  have : IsClosedImmersion (I.subschemeι ∣_ ⊤) := inferInstance
  have : IsIso (adj.unit.app F) := by
    refine isIso_of_bijective_app _ fun V => ?_
    refine bijective_unit_app_of_le I.subschemeι F ⊤ (fun V hV _ a ha m => ?_) V le_top
    have hker : a ∈ RingHom.ker (I.subschemeι.app V).hom := ha
    rw [I.ker_subschemeι_app ⟨V, hV⟩] at hker
    exact mem_annihilatorIdeal.1 hker m
  exact ⟨(asIso (adj.unit.app F)).symm⟩

end Support

end

end GroundTheory.Arith.SchemeCoh
