import Mathlib

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace GlobalTheory.QCoh

variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}

abbrev resAlgebra (h : V ≤ U) : Algebra Γ(X, U) Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom.toAlgebra

abbrev resModule (h : V ≤ U) : Module Γ(X, U) Γ(F, V) :=
  Module.compHom Γ(F, V) (X.presheaf.map (homOfLE h).op).hom

theorem resModule_smul (h : V ≤ U) (r : Γ(X, U)) (s : Γ(F, V)) :
    letI := resModule F h
    r • s = X.presheaf.map (homOfLE h).op r • s := rfl

theorem res_isScalarTower (h : V ≤ U) :
    letI := resAlgebra h
    letI := resModule F h
    IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V) :=
  letI := resAlgebra h
  letI := resModule F h
  .of_algebraMap_smul fun _ _ ↦ rfl

def resLinear (h : V ≤ U) :
    letI := resModule F h
    Γ(F, U) →ₗ[Γ(X, U)] Γ(F, V) :=
  letI := resModule F h
  { toFun := F.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r s ↦ F.map_smul (homOfLE h) r s }

@[simp]
theorem resLinear_apply (h : V ≤ U) (s : Γ(F, U)) :
    resLinear F h s = F.presheaf.map (homOfLE h).op s := rfl

instance moduleSectionsBasicOpen (f : Γ(X, U)) : Module Γ(X, U) Γ(F, X.basicOpen f) :=
  resModule F (X.basicOpen_le f)

instance isScalarTower_sectionsBasicOpen (f : Γ(X, U)) :
    IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) :=
  res_isScalarTower F (X.basicOpen_le f)

def resBasicOpen (f : Γ(X, U)) : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, X.basicOpen f) :=
  resLinear F (X.basicOpen_le f)

@[simp]
theorem resBasicOpen_apply (f : Γ(X, U)) (s : Γ(F, U)) :
    resBasicOpen F f s = F.presheaf.map (homOfLE (X.basicOpen_le f)).op s := rfl

theorem res_res (h : V ≤ U) (h' : W ≤ V) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE h').op (F.presheaf.map (homOfLE h).op s) =
      F.presheaf.map (homOfLE (h'.trans h)).op s := by
  rw [← F.presheaf.map_comp_apply]; rfl

theorem res_self (h : U ≤ U) (s : Γ(F, U)) : F.presheaf.map (homOfLE h).op s = s := by
  have : (homOfLE h).op = 𝟙 (op U) := rfl
  rw [this, F.presheaf.map_id]; rfl

theorem res_res_ring (h : V ≤ U) (h' : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE (h'.trans h)).op s := by
  rw [← X.presheaf.map_comp_apply]; rfl

theorem res_self_ring (h : U ≤ U) (s : Γ(X, U)) : X.presheaf.map (homOfLE h).op s = s := by
  have : (homOfLE h).op = 𝟙 (op U) := rfl
  rw [this, X.presheaf.map_id]; rfl

theorem isUnit_res_of_le_basicOpen (f : Γ(X, U)) (h : V ≤ U) (hV : V ≤ X.basicOpen f) :
    IsUnit (X.presheaf.map (homOfLE h).op f) := by
  rw [← res_res_ring (X.basicOpen_le f) hV]
  exact (X.toRingedSpace.isUnit_res_basicOpen f).map _

theorem isLocalizedModule_resBasicOpen_iff (f : Γ(X, U)) :
    IsLocalizedModule.Away f (resBasicOpen F f) ↔
      (∀ s : Γ(F, X.basicOpen f), ∃ (n : ℕ) (t : Γ(F, U)),
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s =
          F.presheaf.map (homOfLE (X.basicOpen_le f)).op t) ∧
      (∀ t : Γ(F, U), F.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0 →
        ∃ n : ℕ, f ^ n • t = 0) := by
  constructor
  · intro h
    refine ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
    · obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj (resBasicOpen F f) f s
      exact ⟨n, t, by rw [← map_pow]; exact ht⟩
    · obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (f := resBasicOpen F f) f
        (x := t) (y := 0) (by rw [map_zero]; exact ht)
      exact ⟨n, by simpa using hn⟩
  · rintro ⟨h₁, h₂⟩
    refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ (fun s ↦ ?_) h₂
    · have := (isUnit_res_of_le_basicOpen f (X.basicOpen_le f) le_rfl).map
        (algebraMap Γ(X, X.basicOpen f) (Module.End Γ(X, X.basicOpen f) Γ(F, X.basicOpen f)))
      rw [Module.End.isUnit_iff] at this ⊢
      exact this
    · obtain ⟨n, t, ht⟩ := h₁ s
      exact ⟨n, t, by rw [← map_pow] at ht; exact ht⟩

section Spec

variable (hU : IsAffineOpen U)

theorem fromSpec_image_le (W : (Spec Γ(X, U)).Opens) : hU.fromSpec ''ᵁ W ≤ U :=
  (hU.fromSpec.image_le_opensRange W).trans hU.opensRange_fromSpec.le

theorem fromSpec_appIso_inv_res (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U)) :
    (hU.fromSpec.appIso W).inv
      ((Spec Γ(X, U)).presheaf.map W.leTop.op ((Scheme.ΓSpecIso Γ(X, U)).inv r)) =
      X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r := by
  have : X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op ≫ (hU.fromSpec.appIso W).hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map W.leTop.op := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE, hU.fromSpec_app_self,
      Category.assoc, ← Functor.map_comp]
    rfl
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Category.assoc, ← this]
  simp

theorem restrict_fromSpec_smul (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U))
    (s : Γ(F.restrict hU.fromSpec, W)) :
    (F.restrictAppIso hU.fromSpec W).hom (r • s) =
      X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r •
        (F.restrictAppIso hU.fromSpec W).hom s := by
  rw [← fromSpec_appIso_inv_res]
  rfl

theorem isLocalizing_restrict_fromSpec_iff :
    IsLocalizing (modulesSpecToSheaf.obj (F.restrict hU.fromSpec)) ↔
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f) := by
  refine forall_congr' fun f ↦ ?_
  rw [isLocalizedModule_resBasicOpen_iff]
  have key : ∀ (U' V' : X.Opens) (hU' : U' ≤ U) (hV' : V' ≤ U'), U' = U → V' = X.basicOpen f →
      (((∀ s : Γ(F, V'), ∃ (n : ℕ) (t : Γ(F, U')),
        X.presheaf.map (homOfLE (hV'.trans hU')).op (f ^ n) • s =
          F.presheaf.map (homOfLE hV').op t) ∧
      (∀ t : Γ(F, U'), F.presheaf.map (homOfLE hV').op t = 0 →
        ∃ n : ℕ, X.presheaf.map (homOfLE hU').op (f ^ n) • t = 0)) ↔
      ((∀ s : Γ(F, X.basicOpen f), ∃ (n : ℕ) (t : Γ(F, U)),
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s =
          F.presheaf.map (homOfLE (X.basicOpen_le f)).op t) ∧
      (∀ t : Γ(F, U), F.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0 →
        ∃ n : ℕ, f ^ n • t = 0))) := by
    intro U' V' hU' hV' e e'
    subst e e'
    simp only [res_self_ring, map_pow]
  rw [← key (hU.fromSpec ''ᵁ ⊤) (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen f)
    (fromSpec_image_le hU _) (hU.fromSpec.image_mono le_top)
    (by rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec])
    (hU.fromSpec_image_basicOpen f)]
  let φ := ((modulesSpecToSheaf.obj (F.restrict hU.fromSpec)).obj.map
    (PrimeSpectrum.basicOpen f).leTop.op).hom
  constructor
  · intro h
    have h : IsLocalizedModule.Away f φ := h
    refine ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
    · obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj φ f s
      exact ⟨n, t, (restrict_fromSpec_smul F hU _ (f ^ n) s).symm.trans ht⟩
    · obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (f := φ) f
        (x := t) (y := 0) (by rw [map_zero]; exact ht)
      rw [smul_zero] at hn
      exact ⟨n, (restrict_fromSpec_smul F hU _ (f ^ n) t).symm.trans hn⟩
  · rintro ⟨h₁, h₂⟩
    refine IsLocalizedModule.Away.mk_of_addCommGroup (f := φ) ?_ (fun s ↦ ?_) (fun t ht ↦ ?_)
    · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
    · obtain ⟨n, t, ht⟩ := h₁ s
      exact ⟨n, t, (restrict_fromSpec_smul F hU _ (f ^ n) s).trans ht⟩
    · obtain ⟨n, hn⟩ := h₂ t ht
      exact ⟨n, (restrict_fromSpec_smul F hU _ (f ^ n) t).trans hn⟩

end Spec

theorem isQuasicoherent_restrict_fromSpec_iff (hU : IsAffineOpen U) :
    (F.restrict hU.fromSpec).IsQuasicoherent ↔
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f) := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ, isIso_fromTildeΓ_iff_isLocalizing,
    isLocalizing_restrict_fromSpec_iff]

theorem isLocalizedModule_resBasicOpen [F.IsQuasicoherent] (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsLocalizedModule.Away f (resBasicOpen F f) :=
  (isQuasicoherent_restrict_fromSpec_iff F hU).mp inferInstance f

set_option backward.isDefEq.respectTransparency false in

theorem nonempty_presentation_Spec {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] : Nonempty M.Presentation :=
  haveI := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  ⟨SheafOfModules.Presentation.ofIsIso.{u, u, u} M.fromTildeΓ
    (presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _))⟩

set_option backward.isDefEq.respectTransparency false in
theorem nonempty_presentation_over_of_restrict (P : (F.restrict U.ι).Presentation) :
    Nonempty (F.over U).Presentation := by
  let e := Scheme.Modules.overEquiv U
  have : Limits.PreservesColimitsOfSize.{u, u} e.inverse := inferInstance
  let iso : e.inverse.obj (F.restrict U.ι) ≅ F.over U :=
    e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app F).symm ≪≫
      (e.unitIso.app (F.over U)).symm
  exact ⟨SheafOfModules.Presentation.ofIsIso.{u, u, u} iso.hom
    (P.map e.inverse (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm)⟩

set_option backward.isDefEq.respectTransparency false in
theorem nonempty_presentation_restrict_ι (hU : IsAffineOpen U)
    [(F.restrict hU.fromSpec).IsQuasicoherent] : Nonempty (F.restrict U.ι).Presentation := by
  obtain ⟨P⟩ := nonempty_presentation_Spec (F.restrict hU.fromSpec)
  let iso : Scheme.Modules.restrictFunctor hU.fromSpec ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom ≅ Scheme.Modules.restrictFunctor U.ι :=
    (Scheme.Modules.restrictFunctorComp _ _).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec
  exact ⟨SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso.app F).hom
    (Scheme.Modules.presentationRestrict hU.isoSpec.hom P)⟩

set_option backward.isDefEq.respectTransparency false in

theorem isQuasicoherent_of_affineCover {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰)
    (haff : ∀ i, IsAffineOpen (𝒰 i))
    (h : ∀ i (f : Γ(X, 𝒰 i)), IsLocalizedModule.Away f (resBasicOpen F f)) :
    F.IsQuasicoherent := by
  have H (i : ι) : Nonempty (F.over (𝒰 i)).Presentation := by
    have := (isQuasicoherent_restrict_fromSpec_iff F (haff i)).mpr (h i)
    obtain ⟨P⟩ := nonempty_presentation_restrict_ι F (haff i)
    exact nonempty_presentation_over_of_restrict F P
  refine SheafOfModules.QuasicoherentData.isQuasicoherent (M := F)
    { I := ι, X := 𝒰, coversTop := ?_, presentation := fun i ↦ (H i).some }
  rw [Opens.coversTop_iff]
  exact hcov

theorem isQuasicoherent_of_forall_exists_affine
    (h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f)) :
    F.IsQuasicoherent := by
  choose 𝒰 haff hx hloc using h
  refine isQuasicoherent_of_affineCover F 𝒰 ?_ haff hloc
  rw [IsOpenCover, eq_top_iff]
  exact fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩

theorem isQuasicoherent_iff_forall_affine :
    F.IsQuasicoherent ↔ ∀ U : X.Opens, IsAffineOpen U →
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f) := by
  refine ⟨fun _ U hU f ↦ isLocalizedModule_resBasicOpen F hU f, fun h ↦ ?_⟩
  refine isQuasicoherent_of_forall_exists_affine F fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨U, hU, hx, h U hU⟩

theorem isQuasicoherent_iff_affineCover {ι : Type*} (𝒰 : ι → X.Opens) (hcov : IsOpenCover 𝒰)
    (haff : ∀ i, IsAffineOpen (𝒰 i)) :
    F.IsQuasicoherent ↔ ∀ i (f : Γ(X, 𝒰 i)), IsLocalizedModule.Away f (resBasicOpen F f) :=
  ⟨fun _ i f ↦ isLocalizedModule_resBasicOpen F (haff i) f,
    isQuasicoherent_of_affineCover F 𝒰 hcov haff⟩

set_option backward.isDefEq.respectTransparency false in

theorem isQuasicoherent_of_restrict {ι : Type*} {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (g i)] (hcov : ∀ x : X, ∃ i, x ∈ (g i).opensRange)
    (h : ∀ i, (F.restrict (g i)).IsQuasicoherent) : F.IsQuasicoherent := by
  refine isQuasicoherent_of_forall_exists_affine F fun x ↦ ?_
  obtain ⟨i, hi⟩ := hcov x
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, hUi⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hi (g i).opensRange.2
  have hU : IsAffineOpen U := hU
  refine ⟨U, hU, hx, (isQuasicoherent_restrict_fromSpec_iff F hU).mp ?_⟩
  have hr : Set.range hU.fromSpec ⊆ Set.range (g i) := by
    rw [hU.range_fromSpec]; exact hUi
  let l := IsOpenImmersion.lift (g i) hU.fromSpec hr
  have hl : l ≫ g i = hU.fromSpec := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (l ≫ g i) := hl ▸ inferInstance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l (g i)
  let iso : Scheme.Modules.restrictFunctor (g i) ⋙
      Scheme.Modules.restrictFunctor l ≅ Scheme.Modules.restrictFunctor hU.fromSpec :=
    (Scheme.Modules.restrictFunctorComp _ _).symm ≪≫ Scheme.Modules.restrictFunctorCongr hl
  have := h i
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso (iso.app F)
    (inferInstanceAs ((F.restrict (g i)).restrict l).IsQuasicoherent)

section Elementwise

variable [F.IsQuasicoherent]

theorem exists_pow_smul_eq_res (hU : IsAffineOpen U) (f : Γ(X, U)) (h : V ≤ U)
    (hV : V = X.basicOpen f) (s : Γ(F, V)) :
    ∃ (n : ℕ) (t : Γ(F, U)),
      X.presheaf.map (homOfLE h).op f ^ n • s = F.presheaf.map (homOfLE h).op t := by
  subst hV
  exact ((isLocalizedModule_resBasicOpen_iff F f).mp (isLocalizedModule_resBasicOpen F hU f)).1 s

theorem exists_pow_smul_eq_zero (hU : IsAffineOpen U) (f : Γ(X, U)) (h : V ≤ U)
    (hV : V = X.basicOpen f) (t : Γ(F, U)) (ht : F.presheaf.map (homOfLE h).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  subst hV
  exact ((isLocalizedModule_resBasicOpen_iff F f).mp (isLocalizedModule_resBasicOpen F hU f)).2 t ht

theorem isLocalizedModule_resLinear (hU : IsAffineOpen U) (f : Γ(X, U)) (h : V ≤ U)
    (hV : V = X.basicOpen f) :
    letI := resModule F h
    IsLocalizedModule.Away f (resLinear F h) := by
  subst hV
  exact isLocalizedModule_resBasicOpen F hU f

theorem isLocalizedModule_of_ringHom (hU : IsAffineOpen U) {A : Type*} [CommRing A]
    (φ : A →+* Γ(X, U)) (a : A) (h : V ≤ U) (hV : V = X.basicOpen (φ a))
    [Module A Γ(F, U)] [Module A Γ(F, V)]
    (hsU : ∀ (r : A) (s : Γ(F, U)), r • s = φ r • s)
    (hsV : ∀ (r : A) (s : Γ(F, V)), r • s = X.presheaf.map (homOfLE h).op (φ r) • s)
    (l : Γ(F, U) →ₗ[A] Γ(F, V)) (hl : ∀ s, l s = F.presheaf.map (homOfLE h).op s) :
    IsLocalizedModule.Away a l := by
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ (fun s ↦ ?_) (fun t ht ↦ ?_)
  · have := (isUnit_res_of_le_basicOpen (φ a) h hV.le).map
      (algebraMap Γ(X, V) (Module.End Γ(X, V) Γ(F, V)))
    rw [Module.End.isUnit_iff] at this ⊢
    convert this using 1
    ext s
    exact hsV a s
  · obtain ⟨n, t, ht⟩ := exists_pow_smul_eq_res F hU (φ a) h hV s
    exact ⟨n, t, by rw [hsV, hl, map_pow, map_pow, ht]⟩
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero F hU (φ a) h hV t (by rw [← hl, ht])
    exact ⟨n, by rw [hsU, map_pow, hn]⟩

end Elementwise

section Algebra

theorem bijective_of_isLocalizedModule_comp {B M N : Type*} [CommRing B] [AddCommGroup M]
    [Module B M] [AddCommGroup N] [Module B N] (φ : M →ₗ[B] N) (s : Set B)
    (hs : Ideal.span s = ⊤) (P : s → Type*) [∀ b, AddCommGroup (P b)] [∀ b, Module B (P b)]
    (g : ∀ b, N →ₗ[B] P b) [∀ b : s, IsLocalizedModule.Away b.1 (g b)]
    [∀ b : s, IsLocalizedModule.Away b.1 (g b ∘ₗ φ)] : Function.Bijective φ := by
  refine bijective_of_isLocalized_span s hs P (fun b ↦ g b ∘ₗ φ) P g φ fun b ↦ ?_
  have : IsLocalizedModule.map (.powers b.1) (g b ∘ₗ φ) (g b) φ = LinearMap.id := by
    refine IsLocalizedModule.linearMap_ext (.powers b.1) (g b ∘ₗ φ) (g b) ?_
    rw [IsLocalizedModule.map_comp]
    rfl
  rw [this]
  exact Function.bijective_id

theorem isLocalizedModule_comp_liftBaseChange {A B M N P : Type*} (C : Type*) [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] [AddCommGroup P] [Module A P] [Module B P] [Module C P]
    [IsScalarTower A B P] [IsScalarTower A C P] [IsScalarTower B C P]
    (l : M →ₗ[A] N) (g : N →ₗ[B] P) (S : Submonoid B) [IsLocalization S C]
    (h : IsBaseChange C (g.restrictScalars A ∘ₗ l)) :
    IsLocalizedModule S (g ∘ₗ l.liftBaseChange B) := by
  rw [isLocalizedModule_iff_isBaseChange S C]
  refine (TensorProduct.isBaseChange A M B).of_comp ?_
  convert h using 1
  ext m
  simp

end Algebra

theorem isBaseChange_resLinear [F.IsQuasicoherent] (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) :
    letI := resAlgebra h
    letI := resModule F h
    haveI := res_isScalarTower F h
    IsBaseChange Γ(X, V) (resLinear F h) := by
  letI := resAlgebra h
  letI := resModule F h
  haveI := res_isScalarTower F h
  let s : Set Γ(X, V) := {b | ∃ f : Γ(X, U), X.basicOpen b = X.basicOpen f}
  have hs : Ideal.span s = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hU hV x ⟨h hx, hx⟩
    exact Opens.mem_iSup.mpr ⟨⟨g, f, e.symm⟩, e ▸ hxf⟩
  have H₁ (b : s) : IsLocalizedModule.Away b.1 (resBasicOpen F b.1) :=
    isLocalizedModule_resBasicOpen F hV b.1
  have H₂ (b : s) : IsLocalizedModule.Away b.1
      (resBasicOpen F b.1 ∘ₗ (resLinear F h).liftBaseChange Γ(X, V)) := by
    obtain ⟨b, f, e⟩ := b
    have hb : X.basicOpen b ≤ U := (X.basicOpen_le b).trans h
    letI := resAlgebra hb
    letI := resModule F hb
    haveI := res_isScalarTower F hb
    haveI : IsScalarTower Γ(X, U) Γ(X, V) Γ(X, X.basicOpen b) :=
      .of_algebraMap_eq fun r ↦ (res_res_ring h (X.basicOpen_le b) r).symm
    haveI : IsScalarTower Γ(X, U) Γ(X, V) Γ(F, X.basicOpen b) :=
      .of_algebraMap_smul fun r t ↦ by
        change X.presheaf.map (homOfLE (X.basicOpen_le b)).op
          (X.presheaf.map (homOfLE h).op r) • t = X.presheaf.map (homOfLE hb).op r • t
        rw [res_res_ring]
    haveI := hV.isLocalization_basicOpen b
    haveI : IsLocalization.Away f Γ(X, X.basicOpen b) :=
      hU.isLocalization_of_eq_basicOpen f (homOfLE hb) e
    refine isLocalizedModule_comp_liftBaseChange Γ(X, X.basicOpen b) _ _ _ ?_
    rw [← isLocalizedModule_iff_isBaseChange (.powers f)]
    convert isLocalizedModule_resLinear F hU f hb e using 1
    ext t
    exact res_res F h (X.basicOpen_le b) t
  have hbij := bijective_of_isLocalizedModule_comp ((resLinear F h).liftBaseChange Γ(X, V)) s hs
    (fun b ↦ Γ(F, X.basicOpen b.1)) (fun b ↦ resBasicOpen F b.1)
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) fun t ↦ by simp

theorem isBaseChange_of_eq_res [F.IsQuasicoherent] (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) [alg : Algebra Γ(X, U) Γ(X, V)] [mod : Module Γ(X, U) Γ(F, V)]
    [IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V)]
    (halg : ∀ r, algebraMap Γ(X, U) Γ(X, V) r = X.presheaf.map (homOfLE h).op r)
    (l : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, V)) (hl : ∀ s, l s = F.presheaf.map (homOfLE h).op s) :
    IsBaseChange Γ(X, V) l := by
  obtain rfl : mod = resModule F h := Module.ext' _ _ fun r s ↦ by
    rw [resModule_smul, ← halg, algebraMap_smul]
  obtain rfl : alg = resAlgebra h := Algebra.algebra_ext _ _ halg
  letI := resModule F h
  obtain rfl : l = resLinear F h := LinearMap.ext hl
  exact isBaseChange_resLinear F hU hV h

theorem isQuasicoherent_iff_isBaseChange :
    F.IsQuasicoherent ↔ ∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → ∀ h : V ≤ U,
      letI := resAlgebra h
      letI := resModule F h
      haveI := res_isScalarTower F h
      IsBaseChange Γ(X, V) (resLinear F h) := by
  refine ⟨fun _ _ _ hU hV h ↦ isBaseChange_resLinear F hU hV h, fun H ↦ ?_⟩
  refine (isQuasicoherent_iff_forall_affine F).mpr fun U hU f ↦ ?_
  haveI := hU.isLocalization_basicOpen f
  exact (isLocalizedModule_iff_isBaseChange (.powers f) Γ(X, X.basicOpen f) _).mpr
    (H U _ hU (hU.basicOpen f) (X.basicOpen_le f))

section Stalk

instance stalkModule (x : X) : Module (X.presheaf.stalk x) (F.presheaf.stalk x :) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x

theorem germ_smul (x : X) (hx : x ∈ U) (r : Γ(X, U)) (s : Γ(F, U)) :
    F.presheaf.germ U x hx (r • s) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx s :=
  PresheafOfModules.germ_smul (R := X.presheaf) F.val x U hx r s

instance stalkModuleSections (x : U) : Module Γ(X, U) (F.presheaf.stalk (x : X) :) :=
  Module.compHom _ (X.presheaf.germ U x x.2).hom

theorem stalkModuleSections_smul (x : U) (r : Γ(X, U)) (t : (F.presheaf.stalk (x : X) :)) :
    r • t = X.presheaf.germ U x x.2 r • t := rfl

instance isScalarTower_stalk (x : U) :
    IsScalarTower Γ(X, U) (X.presheaf.stalk (x : X)) (F.presheaf.stalk (x : X) :) :=
  .of_algebraMap_smul fun _ _ ↦ rfl

def germLinear (x : U) : Γ(F, U) →ₗ[Γ(X, U)] (F.presheaf.stalk (x : X) :) where
  toFun := F.presheaf.germ U x x.2
  map_add' := map_add _
  map_smul' r s := germ_smul F x x.2 r s

@[simp]
theorem germLinear_apply (x : U) (s : Γ(F, U)) :
    germLinear F x s = F.presheaf.germ U x x.2 s := rfl

theorem mem_primeCompl_primeIdealOf_iff (hU : IsAffineOpen U) (x : U) (f : Γ(X, U)) :
    f ∈ (hU.primeIdealOf x).asIdeal.primeCompl ↔ (x : X) ∈ X.basicOpen f := by
  have := hU.isLocalization_stalk x
  rw [X.mem_basicOpen']
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (x : X))
    (hU.primeIdealOf x).asIdeal f).symm

theorem isLocalizedModule_germLinear [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (germLinear F x) where
  map_units r := by
    have hr := (X.mem_basicOpen' r.1 x).mp ((mem_primeCompl_primeIdealOf_iff hU x r.1).mp r.2)
    have := hr.map (algebraMap (X.presheaf.stalk (x : X))
      (Module.End (X.presheaf.stalk (x : X)) (F.presheaf.stalk (x : X) :)))
    rw [Module.End.isUnit_iff] at this ⊢
    exact this
  surj t := by
    obtain ⟨W, hxW, s, rfl⟩ := F.presheaf.exists_germ_eq t
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ x.2
    obtain ⟨n, t, ht⟩ := exists_pow_smul_eq_res F hU f (X.basicOpen_le f) rfl
      (F.presheaf.map (homOfLE hfW).op s)
    refine ⟨⟨t, ⟨f ^ n, pow_mem ((mem_primeCompl_primeIdealOf_iff hU x f).mpr hxf) n⟩⟩, ?_⟩
    have := congr(F.presheaf.germ _ x hxf $ht)
    rw [germ_smul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ← map_pow,
      TopCat.Presheaf.germ_res_apply] at this
    exact this
  exists_of_eq {s t} e := by
    obtain ⟨W, hxW, i, j, e'⟩ := F.presheaf.germ_eq x x.2 x.2 s t e
    obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ x.2
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero F hU f (X.basicOpen_le f) rfl (s - t) (by
      have e'' : F.presheaf.map (homOfLE i.le).op s = F.presheaf.map (homOfLE i.le).op t := e'
      rw [← res_res F i.le hfW, map_sub, e'', sub_self, map_zero])
    refine ⟨⟨f ^ n, pow_mem ((mem_primeCompl_primeIdealOf_iff hU x f).mpr hxf) n⟩, ?_⟩
    rw [smul_sub, sub_eq_zero] at hn
    exact hn

theorem isBaseChange_germLinear [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    IsBaseChange (X.presheaf.stalk (x : X)) (germLinear F x) :=
  haveI := hU.isLocalization_stalk x
  (isLocalizedModule_iff_isBaseChange (hU.primeIdealOf x).asIdeal.primeCompl _ _).mp
    (isLocalizedModule_germLinear F hU x)

end Stalk

theorem isQuasicoherent_tfae :
    List.TFAE [F.IsQuasicoherent,
      ∀ U : X.Opens, IsAffineOpen U →
        ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f),
      ∃ (ι : Type u) (𝒰 : ι → X.Opens), IsOpenCover 𝒰 ∧ (∀ i, IsAffineOpen (𝒰 i)) ∧
        ∀ i (f : Γ(X, 𝒰 i)), IsLocalizedModule.Away f (resBasicOpen F f)] := by
  tfae_have 1 ↔ 2 := isQuasicoherent_iff_forall_affine F
  tfae_have 2 → 3 := fun h ↦
    ⟨X.affineOpens, fun i ↦ i.1, iSup_affineOpens_eq_top X, fun i ↦ i.2, fun i ↦ h i.1 i.2⟩
  tfae_have 3 → 1 := fun ⟨_, 𝒰, hcov, haff, h⟩ ↦ isQuasicoherent_of_affineCover F 𝒰 hcov haff h
  tfae_finish

theorem quasicoherent_local :
    (F.IsQuasicoherent ↔ ∀ U : X.Opens, IsAffineOpen U →
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f)) ∧
    (∀ (ι : Type u) (𝒰 : ι → X.Opens), IsOpenCover 𝒰 → (∀ i, IsAffineOpen (𝒰 i)) →
      (F.IsQuasicoherent ↔
        ∀ i (f : Γ(X, 𝒰 i)), IsLocalizedModule.Away f (resBasicOpen F f))) ∧
    (F.IsQuasicoherent → ∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → ∀ h : V ≤ U,
      letI := resAlgebra h
      letI := resModule F h
      haveI := res_isScalarTower F h
      IsBaseChange Γ(X, V) (resLinear F h)) ∧
    (F.IsQuasicoherent → ∀ (U : X.Opens) (hU : IsAffineOpen U) (x : U),
      IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (germLinear F x)) :=
  ⟨isQuasicoherent_iff_forall_affine F, fun _ ↦ isQuasicoherent_iff_affineCover F,
    fun _ _ _ hU hV h ↦ isBaseChange_resLinear F hU hV h,
    fun _ _ hU x ↦ isLocalizedModule_germLinear F hU x⟩

end GlobalTheory.QCoh
