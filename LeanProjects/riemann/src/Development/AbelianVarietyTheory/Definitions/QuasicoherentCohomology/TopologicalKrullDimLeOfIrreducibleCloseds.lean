import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsLocalizedModuleGermLinearPointOfPrime

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing

universe u

noncomputable section

namespace GlobalTheory.QCoh

variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}

section Finite

class IsFiniteQC (F : X.Modules) : Prop where

  isQuasicoherent : F.IsQuasicoherent

  finite_affine : ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U)

attribute [instance 100] IsFiniteQC.isQuasicoherent

variable (F) in

theorem finite_sections [IsFiniteQC F] (hU : IsAffineOpen U) : Module.Finite Γ(X, U) Γ(F, U) :=
  IsFiniteQC.finite_affine U hU

instance finite_sections_affineOpens [IsFiniteQC F] (U : X.affineOpens) : Module.Finite Γ(X, U) Γ(F, U) :=
  finite_sections F U.2

instance finite_globalSections_of_affine [IsFiniteQC F] [IsAffine X] : Module.Finite Γ(X, ⊤) Γ(F, ⊤) :=
  finite_sections F (isAffineOpen_top X)

theorem exists_affine_mem_le (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact ⟨V, hV, hxV, hVU⟩

theorem exists_affine_mem (x : X) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V :=
  have ⟨V, hV, hx, _⟩ := exists_affine_mem_le (U := ⊤) x trivial
  ⟨V, hV, hx⟩

variable (F) in

theorem finite_stalk_of_finite_sections [F.IsQuasicoherent] (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(F, U)] (x : U) :
    Module.Finite (X.presheaf.stalk (x : X)) (F.presheaf.stalk (x : X) :) :=
  have := hU.isLocalization_stalk x
  have := isLocalizedModule_germLinear F hU x
  Module.Finite.of_isLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (germLinear F x)

instance finite_stalk [IsFiniteQC F] (x : X) :
    Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x :) := by
  obtain ⟨U, hU, hx⟩ := exists_affine_mem x
  have := finite_sections F hU
  exact finite_stalk_of_finite_sections F hU ⟨x, hx⟩

variable (F) in

theorem finite_sections_basicOpen [F.IsQuasicoherent] (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(F, U)] (f : Γ(X, U)) :
    Module.Finite Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) :=
  have := hU.isLocalization_basicOpen f
  have := isLocalizedModule_resBasicOpen F hU f
  Module.Finite.of_isLocalizedModule (.powers f) (resBasicOpen F f)

theorem IsFiniteQC.of_forall_exists_affine [F.IsQuasicoherent]
    (h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ Module.Finite Γ(X, U) Γ(F, U)) :
    IsFiniteQC F := by
  refine ⟨inferInstance, fun U hU ↦ ?_⟩
  let s : Set Γ(X, U) := {f | Module.Finite Γ(X, X.basicOpen f) Γ(F, X.basicOpen f)}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨V, hV, hxV, hfin⟩ := h x
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hU hV x ⟨hx, hxV⟩
    have := finite_sections_basicOpen F hV g
    rw [← e] at this
    exact Opens.mem_iSup.mpr ⟨⟨f, this⟩, hxf⟩
  exact @Module.Finite.of_localizationSpan' _ _ _ _ _ s hs (fun g ↦ Γ(F, X.basicOpen g.1)) _ _
    (fun g ↦ Γ(X, X.basicOpen g.1)) _ _ (fun g ↦ hU.isLocalization_basicOpen g.1) _ _
    (fun g ↦ resBasicOpen F g.1) (fun g ↦ isLocalizedModule_resBasicOpen F hU g.1) fun g ↦ g.2

theorem isFiniteQC_iff_affineCover [F.IsQuasicoherent] {ι : Type*} (𝒰 : ι → X.Opens)
    (hcov : IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i)) :
    IsFiniteQC F ↔ ∀ i, Module.Finite Γ(X, 𝒰 i) Γ(F, 𝒰 i) :=
  ⟨fun _ i ↦ finite_sections F (haff i), fun h ↦ .of_forall_exists_affine fun x ↦
    have ⟨i, hi⟩ := hcov.exists_mem x
    ⟨𝒰 i, haff i, hi, h i⟩⟩

theorem isFiniteQC_iff_finite_top [IsAffine X] [F.IsQuasicoherent] :
    IsFiniteQC F ↔ Module.Finite Γ(X, ⊤) Γ(F, ⊤) :=
  ⟨fun _ ↦ inferInstance, fun h ↦ .of_forall_exists_affine fun _ ↦
    ⟨⊤, isAffineOpen_top X, trivial, h⟩⟩

theorem IsFiniteQC.of_epi (φ : F ⟶ G) [Epi φ] [IsFiniteQC F] [G.IsQuasicoherent] :
    IsFiniteQC G :=
  ⟨inferInstance, fun U hU ↦
    have := finite_sections F hU
    .of_surjective (appLinear φ U) (surjective_app_of_epi φ hU)⟩

theorem IsFiniteQC.of_iso (e : F ≅ G) [IsFiniteQC F] : IsFiniteQC G :=
  have : G.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e IsFiniteQC.isQuasicoherent
  .of_epi e.hom

theorem isFiniteQC_iff_of_iso (e : F ≅ G) : IsFiniteQC F ↔ IsFiniteQC G :=
  ⟨fun _ ↦ .of_iso e, fun _ ↦ .of_iso e.symm⟩

variable (F) in

theorem isNoetherian_sections [IsLocallyNoetherian X] [IsFiniteQC F] (hU : IsAffineOpen U) :
    _root_.IsNoetherian Γ(X, U) Γ(F, U) :=
  have := finite_sections F hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  inferInstance

theorem IsFiniteQC.of_mono [IsLocallyNoetherian X] (φ : F ⟶ G) [Mono φ] [F.IsQuasicoherent]
    [IsFiniteQC G] : IsFiniteQC F :=
  ⟨inferInstance, fun U hU ↦
    have := isNoetherian_sections G hU
    .of_injective (appLinear φ U) (injective_app_of_mono φ U)⟩

theorem IsFiniteQC.of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteQC S.X₁] [S.X₂.IsQuasicoherent] [IsFiniteQC S.X₃] : IsFiniteQC S.X₂ :=
  ⟨inferInstance, fun U hU ↦
    have := hS.epi_g
    have := finite_sections S.X₁ hU
    have := finite_sections S.X₃ hU
    Module.Finite.of_exact (f := appLinear S.f U) (g := appLinear S.g U)
      (exact_app_of_exact hS.exact hU) (surjective_app_of_epi S.g hU)⟩

instance isFiniteQC_cokernel (φ : F ⟶ G) [F.IsQuasicoherent] [IsFiniteQC G] :
    IsFiniteQC (cokernel φ) :=
  .of_epi (cokernel.π φ)

instance isFiniteQC_image (φ : F ⟶ G) [IsFiniteQC F] [G.IsQuasicoherent] :
    IsFiniteQC (image φ) :=
  .of_epi (factorThruImage φ)

instance isFiniteQC_kernel [IsLocallyNoetherian X] (φ : F ⟶ G) [IsFiniteQC F]
    [G.IsQuasicoherent] : IsFiniteQC (kernel φ) :=
  .of_mono (kernel.ι φ)

section Sums

variable {ι : Type*} [Fintype ι] {A : ι → X.Modules} (p : ∀ i, F ⟶ A i) (q : ∀ i, A i ⟶ F)

theorem sum_app_app (h : ∑ i, p i ≫ q i = 𝟙 F) (s : Γ(F, U)) :
    ∑ i, (q i).app U ((p i).app U s) = s := by
  let e : (F ⟶ F) →+ Γ(F, U) := AddMonoidHom.mk' (fun φ ↦ φ.app U s) fun _ _ ↦ rfl
  have := map_sum e (fun i ↦ p i ≫ q i) Finset.univ
  rw [h] at this
  exact this.symm

theorem isQuasicoherent_of_sum_eq_id (h : ∑ i, p i ≫ q i = 𝟙 F) [∀ i, (A i).IsQuasicoherent] :
    F.IsQuasicoherent := by
  refine (isQuasicoherent_iff_forall_affine F).2 fun U hU f ↦
    (isLocalizedModule_resBasicOpen_iff F f).2 ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
  · choose n t ht using fun i ↦
      exists_pow_smul_eq_res (A i) hU f (X.basicOpen_le f) rfl ((p i).app _ s)
    refine ⟨∑ i, n i, ∑ i, (q i).app U (f ^ (∑ j, n j - n i) • t i), ?_⟩
    rw [map_sum, ← sum_app_app p q h s, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi : n i ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    rw [← app_res, Scheme.Modules.map_smul, ← ht, smul_smul, map_pow, ← pow_add,
      Nat.sub_add_cancel hi, Scheme.Modules.Hom.app_smul]
  · choose n hn using fun i ↦ exists_pow_smul_eq_zero (A i) hU f (X.basicOpen_le f) rfl
      ((p i).app _ t) (by rw [← app_res, ht, map_zero])
    refine ⟨∑ i, n i, ?_⟩
    rw [← sum_app_app p q h t, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hi : n i ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    rw [← Scheme.Modules.Hom.app_smul, ← Nat.sub_add_cancel hi, pow_add, mul_smul, hn, smul_zero,
      map_zero]

theorem IsFiniteQC.of_sum_eq_id (h : ∑ i, p i ≫ q i = 𝟙 F) [hA : ∀ i, IsFiniteQC (A i)] :
    IsFiniteQC F := by
  classical
  refine ⟨isQuasicoherent_of_sum_eq_id p q h, fun U hU ↦ ?_⟩
  have (i : ι) := finite_sections (A i) hU
  refine .of_surjective (LinearMap.lsum Γ(X, U) (fun i ↦ Γ(A i, U)) ℕ
    fun i ↦ appLinear (q i) U) fun s ↦ ⟨fun i ↦ (p i).app U s, ?_⟩
  simpa using sum_app_app p q h s

end Sums

theorem IsFiniteQC.of_isZero (h : IsZero F) : IsFiniteQC F :=
  .of_sum_eq_id (ι := Empty) (A := fun i ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim)
    (h.eq_of_src _ _) (hA := fun i ↦ i.elim)

theorem IsFiniteQC.of_isColimit_cofan {ι : Type*} [Finite ι] {A : ι → X.Modules}
    [∀ i, IsFiniteQC (A i)] {c : Cofan A} (hc : IsColimit c) : IsFiniteQC c.pt := by
  classical
  have := Fintype.ofFinite ι
  refine .of_sum_eq_id (fun i ↦ Cofan.IsColimit.desc hc fun j ↦
    if h : j = i then eqToHom (h ▸ rfl) else 0) c.inj (Cofan.IsColimit.hom_ext hc _ _ fun j ↦ ?_)
  simp [Preadditive.comp_sum, Cofan.IsColimit.fac_assoc, dite_comp]

theorem IsFiniteQC.of_isLimit_fan {ι : Type*} [Finite ι] {A : ι → X.Modules}
    [∀ i, IsFiniteQC (A i)] {c : Fan A} (hc : IsLimit c) : IsFiniteQC c.pt := by
  classical
  have := Fintype.ofFinite ι
  refine .of_sum_eq_id c.proj (fun i ↦ Fan.IsLimit.lift hc fun j ↦
    if h : i = j then eqToHom (h ▸ rfl) else 0) (Fan.IsLimit.hom_ext hc _ _ fun j ↦ ?_)
  simp [Preadditive.sum_comp, Fan.IsLimit.fac, comp_dite]

instance isFiniteQC_sigmaObj {ι : Type*} [Finite ι] (A : ι → X.Modules) [HasCoproduct A]
    [∀ i, IsFiniteQC (A i)] :
    IsFiniteQC (∐ A) :=
  .of_isColimit_cofan (coproductIsCoproduct A)

instance isFiniteQC_piObj {ι : Type*} [Finite ι] (A : ι → X.Modules) [HasProduct A]
    [∀ i, IsFiniteQC (A i)] :
    IsFiniteQC (∏ᶜ A) :=
  .of_isLimit_fan (productIsProduct A)

instance isFiniteQC_biproduct {ι : Type*} [Finite ι] (A : ι → X.Modules) [HasBiproduct A]
    [∀ i, IsFiniteQC (A i)] :
    IsFiniteQC (⨁ A) :=
  .of_isLimit_fan (biproduct.isLimit A)

instance isFiniteQC_biprod [IsFiniteQC F] [IsFiniteQC G] : IsFiniteQC (F ⊞ G) :=
  .of_sum_eq_id (ι := Bool) (A := fun b ↦ b.casesOn F G)
    (fun b ↦ b.casesOn biprod.fst biprod.snd) (fun b ↦ b.casesOn biprod.inl biprod.inr)
    (by rw [Fintype.sum_bool, add_comm]; exact biprod.total)
    (hA := fun b ↦ b.casesOn ‹IsFiniteQC F› ‹IsFiniteQC G›)

variable (X) in

abbrev structureModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

variable (X) in

abbrev freeModule (ι : Type u) : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) ι

variable (U) in

def structureModuleSectionsEquiv : Γ(structureModule X, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  LinearEquiv.refl Γ(X, U) Γ(X, U)

instance isFiniteQC_structureModule : IsFiniteQC (structureModule X) where
  isQuasicoherent := (isQuasicoherent_iff_forall_affine _).2 fun U hU f ↦
    have := hU.isLocalization_basicOpen f
    inferInstanceAs (IsLocalizedModule (.powers f) (Algebra.linearMap Γ(X, U) Γ(X, X.basicOpen f)))
  finite_affine U _ := inferInstanceAs (Module.Finite Γ(X, U) Γ(X, U))

instance isFiniteQC_freeModule (ι : Type u) [Finite ι] : IsFiniteQC (freeModule X ι) :=
  .of_isColimit_cofan (A := fun _ : ι ↦ structureModule X)
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) ι)

section Restrict

variable {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]

variable (F) in

theorem finite_sections_restrict_iff (W : Y.Opens) :
    Module.Finite Γ(Y, W) Γ(F.restrict g, W) ↔ Module.Finite Γ(X, g ''ᵁ W) Γ(F, g ''ᵁ W) := by
  let σ := (g.appIso W).commRingCatIsoToRingEquiv
  constructor <;> intro h
  · have : RingHomSurjective (σ.symm : Γ(Y, W) →+* Γ(X, g ''ᵁ W)) := ⟨σ.symm.surjective⟩
    let l : Γ(F.restrict g, W) →ₛₗ[(σ.symm : Γ(Y, W) →+* Γ(X, g ''ᵁ W))] Γ(F, g ''ᵁ W) :=
      { toFun := (F.restrictAppIso g W).hom
        map_add' := map_add _
        map_smul' := fun _ _ ↦ rfl }
    exact .of_surjective l (ConcreteCategory.bijective_of_isIso (F.restrictAppIso g W).hom).2
  · have : RingHomSurjective (σ : Γ(X, g ''ᵁ W) →+* Γ(Y, W)) := ⟨σ.surjective⟩
    let l : Γ(F, g ''ᵁ W) →ₛₗ[(σ : Γ(X, g ''ᵁ W) →+* Γ(Y, W))] Γ(F.restrict g, W) :=
      { toFun := (F.restrictAppIso g W).inv
        map_add' := map_add _
        map_smul' := fun r s ↦ F.smul_restrictAppIso_inv_apply g W r s }
    exact .of_surjective l (ConcreteCategory.bijective_of_isIso (F.restrictAppIso g W).inv).2

instance isFiniteQC_restrict [IsFiniteQC F] : IsFiniteQC (F.restrict g) :=
  ⟨inferInstance, fun W hW ↦ (finite_sections_restrict_iff F g W).2
    (finite_sections F (hW.image_of_isOpenImmersion g))⟩

theorem IsFiniteQC.of_restrict {ι : Type*} {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (g i)] (hcov : ∀ x : X, ∃ i, x ∈ (g i).opensRange)
    (h : ∀ i, IsFiniteQC (F.restrict (g i))) : IsFiniteQC F := by
  have := isQuasicoherent_of_restrict F g hcov fun i ↦ (h i).isQuasicoherent
  refine .of_forall_exists_affine fun x ↦ ?_
  obtain ⟨i, y, rfl⟩ := hcov x
  obtain ⟨W, hW, hy⟩ := exists_affine_mem y
  exact ⟨g i ''ᵁ W, hW.image_of_isOpenImmersion _, ⟨y, hy, rfl⟩,
    (finite_sections_restrict_iff F (g i) W).1 ((h i).finite_affine W hW)⟩

end Restrict

end Finite

section Tilde

variable {R : CommRingCat.{u}}

def tildeTopEquiv (M : ModuleCat.{u} R) : M ≃ₗ[R] Γ(tilde M, ⊤) :=
  (tilde.isoTop M).toLinearEquiv

theorem algebraMap_Spec_top_bijective : Function.Bijective (algebraMap R Γ(Spec R, ⊤)) := by
  have : ⇑(algebraMap R Γ(Spec R, ⊤)) = (Scheme.ΓSpecIso R).inv := rfl
  rw [this]
  exact ConcreteCategory.bijective_of_isIso _

theorem isFiniteQC_Spec_iff (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsFiniteQC M ↔ Module.Finite R Γ(M, ⊤) := by
  rw [isFiniteQC_iff_finite_top]
  refine ⟨fun _ ↦ ?_, fun _ ↦ .of_restrictScalars_finite R _ _⟩
  have : Module.Finite R Γ(Spec R, ⊤) :=
    .of_surjective (Algebra.linearMap R _) algebraMap_Spec_top_bijective.2
  exact .trans Γ(Spec R, ⊤) _

theorem isFiniteQC_tilde_iff (M : ModuleCat.{u} R) : IsFiniteQC (tilde M) ↔ Module.Finite R M := by
  rw [isFiniteQC_Spec_iff]
  exact (Module.Finite.equiv_iff (tildeTopEquiv M)).symm

instance isFiniteQC_tilde (M : ModuleCat.{u} R) [Module.Finite R M] : IsFiniteQC (tilde M) :=
  (isFiniteQC_tilde_iff M).2 ‹_›

theorem not_isFiniteQC_tilde_rat :
    ¬ IsFiniteQC (tilde (R := CommRingCat.of ℤ) (ModuleCat.of ℤ ℚ)) := by
  rw [isFiniteQC_tilde_iff]
  intro h
  have h : Module.Finite ℤ ℚ := h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ) (x := 1 / 2) |>.1
    (Algebra.IsIntegral.isIntegral _)
  have : ((2 * n : ℤ) : ℚ) = (1 : ℤ) := by
    have hn : (n : ℚ) = 1 / 2 := hn
    push_cast
    rw [hn]; norm_num
  have := Int.cast_injective this
  omega

end Tilde

section FiniteType

set_option backward.isDefEq.respectTransparency false in

theorem IsFiniteQC.of_generatingSections [F.IsQuasicoherent] (σ : F.GeneratingSections)
    [σ.IsFiniteType] : IsFiniteQC F :=
  have : Epi (C := X.Modules) (X := freeModule X σ.I) (Y := F) σ.π := σ.epi
  .of_epi (F := freeModule X σ.I) σ.π

set_option backward.isDefEq.respectTransparency false in

theorem IsFiniteQC.of_isFiniteType [F.IsQuasicoherent] [F.IsFiniteType] : IsFiniteQC F := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  refine .of_restrict (fun i ↦ Scheme.Opens.ι (σ.X i)) (fun x ↦ ?_) fun i ↦ ?_
  · obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ _).1 σ.coversTop).exists_mem x
    exact ⟨i, by simpa using hi⟩
  · let e := Scheme.Modules.overEquiv (σ.X i)
    have : PreservesColimitsOfSize.{u, u} e.functor := inferInstance
    have := hσ.isFiniteType i
    let τ := ((σ.generators i).map e.functor
      (Opens.sheafOfModulesEquivOverUnit (σ.X i) X.ringCatSheaf).symm).ofEpi
      ((Scheme.Modules.overFunctorEquiv (σ.X i)).app F).hom
    have : τ.IsFiniteType := ⟨this.finite⟩
    exact .of_generatingSections τ

set_option backward.isDefEq.respectTransparency false in

theorem exists_presentation_over [F.IsQuasicoherent] (hU : IsAffineOpen U)
    (s : Set Γ(F.restrict hU.fromSpec, ⊤)) (hs : Submodule.span Γ(X, U) s = ⊤)
    (t : Set (s →₀ Γ(X, U))) (ht : Submodule.span Γ(X, U) t =
      LinearMap.ker (Finsupp.linearCombination Γ(X, U) ((↑) : s → Γ(F.restrict hU.fromSpec, ⊤)))) :
    ∃ P : (F.over U).Presentation, P.generators.I = s ∧ P.relations.I = t := by
  let M := F.restrict hU.fromSpec
  have := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let P₁ : M.Presentation := SheafOfModules.Presentation.ofIsIso.{u, u, u} M.fromTildeΓ
    (presentationTilde.{u} _ s hs t ht)
  let iso₁ : Scheme.Modules.restrictFunctor hU.fromSpec ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom ≅ Scheme.Modules.restrictFunctor U.ι :=
    (Scheme.Modules.restrictFunctorComp _ _).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec
  let P₂ : (F.restrict U.ι).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u} (iso₁.app F).hom
      (Scheme.Modules.presentationRestrict hU.isoSpec.hom P₁)
  let e := Scheme.Modules.overEquiv U
  have : PreservesColimitsOfSize.{u, u} e.inverse := inferInstance
  let iso₂ : e.inverse.obj (F.restrict U.ι) ≅ F.over U :=
    e.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app F).symm ≪≫
      (e.unitIso.app (F.over U)).symm
  exact ⟨SheafOfModules.Presentation.ofIsIso.{u, u, u} iso₂.hom
    (P₂.map e.inverse (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm), rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in

instance IsFiniteQC.isFiniteType [IsFiniteQC F] : F.IsFiniteType := by
  have H (U : X.affineOpens) : ∃ σ : (F.over U.1).GeneratingSections, σ.IsFiniteType := by
    obtain ⟨s, hs⟩ := ((isFiniteQC_Spec_iff (F.restrict U.2.fromSpec)).1 inferInstance).fg_top
    obtain ⟨P, hP, -⟩ := exists_presentation_over U.2 (F := F) s hs _ (Submodule.span_eq _)
    exact ⟨P.generators, ⟨hP ▸ inferInstance⟩⟩
  choose σ hσ using H
  let q : SheafOfModules.LocalGeneratorsData.{u, u, u, u} (R := X.ringCatSheaf) F :=
    { I := ↥X.affineOpens, X := fun U ↦ U.1, generators := σ
      coversTop := by rw [Opens.coversTop_iff]; exact iSup_affineOpens_eq_top X }
  have hq : q.IsFiniteType :=
    SheafOfModules.LocalGeneratorsData.IsFiniteType.mk.{u, u, u, u} (p := q) hσ
  exact SheafOfModules.IsFiniteType.mk.{u, u, u} (Exists.intro q hq)

theorem isFiniteQC_iff_isFiniteType : IsFiniteQC F ↔ F.IsQuasicoherent ∧ F.IsFiniteType :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ .of_isFiniteType⟩

set_option backward.isDefEq.respectTransparency false in

theorem IsFiniteQC.of_isFinitePresentation [F.IsFinitePresentation] : IsFiniteQC F :=
  .of_isFiniteType

set_option backward.isDefEq.respectTransparency false in

theorem IsFiniteQC.isFinitePresentation [IsLocallyNoetherian X] [IsFiniteQC F] :
    F.IsFinitePresentation := by
  have H (U : X.affineOpens) : ∃ P : (F.over U.1).Presentation, P.IsFinite := by
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨s, hs⟩ := ((isFiniteQC_Spec_iff (F.restrict U.2.fromSpec)).1 inferInstance).fg_top
    obtain ⟨t, ht⟩ := IsNoetherian.noetherian (LinearMap.ker (Finsupp.linearCombination Γ(X, U.1)
      (Subtype.val : ↥(s : Set Γ(F.restrict U.2.fromSpec, ⊤)) → Γ(F.restrict U.2.fromSpec, ⊤))))
    obtain ⟨P, hP, hP'⟩ := exists_presentation_over U.2 (F := F) s hs t ht
    exact ⟨P, ⟨⟨hP ▸ inferInstance⟩, ⟨hP' ▸ inferInstance⟩⟩⟩
  choose P hP using H
  let q : SheafOfModules.QuasicoherentData.{u, u, u, u} (R := X.ringCatSheaf) F :=
    { I := ↥X.affineOpens, X := fun U ↦ U.1, presentation := P
      coversTop := by rw [Opens.coversTop_iff]; exact iSup_affineOpens_eq_top X }
  have hq : q.IsFinitePresentation :=
    SheafOfModules.QuasicoherentData.IsFinitePresentation.mk.{u, u, u, u} (q := q) hP
  exact SheafOfModules.IsFinitePresentation.mk.{u, u, u} (Exists.intro q hq)

theorem isFiniteQC_iff_isFinitePresentation [IsLocallyNoetherian X] :
    IsFiniteQC F ↔ F.IsFinitePresentation :=
  ⟨fun _ ↦ IsFiniteQC.isFinitePresentation, fun _ ↦ .of_isFinitePresentation⟩

end FiniteType

section Support

variable (F) in

def support : Set X := {x | Nontrivial (F.presheaf.stalk x :)}

theorem mem_support_iff {x : X} : x ∈ support F ↔ Nontrivial (F.presheaf.stalk x :) := Iff.rfl

theorem notMem_support_iff {x : X} : x ∉ support F ↔ Subsingleton (F.presheaf.stalk x :) :=
  not_nontrivial_iff_subsingleton

theorem mem_support_iff_primeIdealOf [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ support F ↔ hU.primeIdealOf x ∈ Module.support Γ(X, U) Γ(F, U) :=
  have := isLocalizedModule_germLinear F hU x
  (IsLocalizedModule.iso (hU.primeIdealOf x).asIdeal.primeCompl
    (germLinear F x)).toEquiv.nontrivial_congr.symm

variable (F) in

theorem fromSpec_preimage_support [F.IsQuasicoherent] (hU : IsAffineOpen U) :
    hU.fromSpec ⁻¹' support F = Module.support Γ(X, U) Γ(F, U) := by
  refine Set.ext fun P : PrimeSpectrum Γ(X, U) ↦ ?_
  have := mem_support_iff_primeIdealOf (F := F) hU (pointOfPrime hU P)
  rwa [primeIdealOf_pointOfPrime] at this

theorem mem_support_iff_annihilator_le [IsFiniteQC F] (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ support F ↔
      Module.annihilator Γ(X, U) Γ(F, U) ≤ (hU.primeIdealOf x).asIdeal :=
  have := finite_sections F hU
  (mem_support_iff_primeIdealOf hU x).trans Module.mem_support_iff_of_finite

variable (F) in

theorem support_inter_eq_zeroLocus [IsFiniteQC F] (hU : IsAffineOpen U) :
    support F ∩ U = X.zeroLocus (U := U) (Module.annihilator Γ(X, U) Γ(F, U)) ∩ U := by
  ext x
  refine and_congr_left fun hx ↦ (mem_support_iff_annihilator_le hU ⟨x, hx⟩).trans ?_
  rw [Scheme.mem_zeroLocus_iff]
  refine forall₂_congr fun f _ ↦ ?_
  rw [← mem_primeCompl_primeIdealOf_iff hU ⟨x, hx⟩ f]
  exact not_not.symm

variable (F) in

theorem isClosed_support [IsFiniteQC F] : IsClosed (support F) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU⟩ := exists_affine_mem x
  refine ⟨(X.zeroLocus (U := U) (Module.annihilator Γ(X, U) Γ(F, U)))ᶜ ∩ U, fun y hy hyF ↦ ?_,
    (X.zeroLocus_isClosed _).isOpen_compl.inter U.2, fun h ↦ ?_, hxU⟩
  · exact hy.1 ((support_inter_eq_zeroLocus F hU).le ⟨hyF, hy.2⟩).1
  · exact hx ((support_inter_eq_zeroLocus F hU).ge ⟨h, hxU⟩).1

theorem mem_support_of_specializes [F.IsQuasicoherent] {x y : X} (h : x ⤳ y)
    (hx : x ∈ support F) : y ∈ support F := by
  obtain ⟨U, hU, hy⟩ := exists_affine_mem y
  have hxU : x ∈ U := h.mem_open U.2 hy
  refine (mem_support_iff_primeIdealOf hU ⟨y, hy⟩).2 (Module.mem_support_mono ?_
    ((mem_support_iff_primeIdealOf hU ⟨x, hxU⟩).1 hx))
  intro f hf
  by_contra hf'
  exact (mem_primeCompl_primeIdealOf_iff hU ⟨x, hxU⟩ f).2 (h.mem_open (X.basicOpen f).2
    ((mem_primeCompl_primeIdealOf_iff hU ⟨y, hy⟩ f).1 hf')) hf

theorem support_subset_of_mono (φ : F ⟶ G) [Mono φ] : support F ⊆ support G :=
  fun x (_ : Nontrivial _) ↦ (stalkLinear_injective φ x).nontrivial

theorem support_subset_of_epi (φ : F ⟶ G) [Epi φ] : support G ⊆ support F :=
  fun x (_ : Nontrivial _) ↦ (stalkLinear_surjective φ x).nontrivial

theorem support_eq_of_iso (e : F ≅ G) : support F = support G :=
  (support_subset_of_mono e.hom).antisymm (support_subset_of_mono e.inv)

theorem support_subset_union_of_exact {S : ShortComplex X.Modules} (hS : S.Exact) :
    support S.X₂ ⊆ support S.X₁ ∪ support S.X₃ := by
  intro x hx
  by_contra h
  rw [Set.mem_union, not_or, notMem_support_iff, notMem_support_iff] at h
  obtain ⟨h₁, h₃⟩ := h
  refine notMem_support_iff.2 (subsingleton_of_forall_eq 0 fun t ↦ ?_) hx
  obtain ⟨s, rfl⟩ := ((exact_iff_stalkLinear S).1 hS x t).1 (Subsingleton.elim _ _)
  rw [Subsingleton.elim s 0, map_zero]

theorem support_eq_union_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    support S.X₂ = support S.X₁ ∪ support S.X₃ :=
  have := hS.mono_f
  have := hS.epi_g
  (support_subset_union_of_exact hS.exact).antisymm
    (Set.union_subset (support_subset_of_mono S.f) (support_subset_of_epi S.g))

theorem support_biprod : support (F ⊞ G) = support F ∪ support G :=
  support_eq_union_of_shortExact (S := ShortComplex.mk (biprod.inl : F ⟶ F ⊞ G) biprod.snd
    biprod.inl_snd) (ShortComplex.Splitting.shortExact
      { r := biprod.fst, s := biprod.inr, f_r := by simp, s_g := by simp, id := by simp })

theorem support_eq_empty_iff : support F = ∅ ↔ IsZero F := by
  constructor
  · intro h
    rw [IsZero.iff_id_eq_zero]
    ext U s
    refine section_eq_zero_of_germ (F := F) s fun x hx ↦ ?_
    have := notMem_support_iff.1 (Set.eq_empty_iff_forall_notMem.1 h x)
    exact Subsingleton.elim _ _
  · intro h
    refine Set.eq_empty_iff_forall_notMem.2 fun x ↦ notMem_support_iff.2 ?_
    have := stalkLinear_id F x
    rw [(IsZero.iff_id_eq_zero F).1 h, stalkLinear_zero] at this
    exact subsingleton_of_forall_eq 0 fun t ↦ congr($this t).symm

variable (F) in

def restrictStalkAddEquiv {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (y : Y) :
    ((F.restrict g).presheaf.stalk y :) ≃+ (F.presheaf.stalk (g y) :) :=
  ((Scheme.Modules.restrictStalkNatIso g y).app F).addCommGroupIsoToAddEquiv

theorem restrictStalkAddEquiv_germ {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (y : Y)
    {W : Y.Opens} (hy : y ∈ W) (s : Γ(F.restrict g, W)) :
    restrictStalkAddEquiv F g y ((F.restrict g).presheaf.germ W y hy s) =
      F.presheaf.germ (g ''ᵁ W) (g y) ⟨y, hy, rfl⟩ ((F.restrictAppIso g W).hom s) :=
  congr($(Scheme.Modules.germ_restrictStalkNatIso_hom_app g y F hy) s)

theorem restrictStalkAddEquiv_smul {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (y : Y)
    (r : X.presheaf.stalk (g y)) (t : ((F.restrict g).presheaf.stalk y :)) :
    restrictStalkAddEquiv F g y (g.stalkMap y r • t) = r • restrictStalkAddEquiv F g y t := by
  obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨W, hW, s, rfl⟩ := (F.restrict g).presheaf.exists_germ_eq t
  have hy : y ∈ W ⊓ g ⁻¹ᵁ U := ⟨hW, hU⟩
  have hle : g ''ᵁ (W ⊓ g ⁻¹ᵁ U) ≤ U := (g.image_mono inf_le_right).trans (g.image_preimage_le U)
  have key : Y.presheaf.map (homOfLE (inf_le_right : W ⊓ g ⁻¹ᵁ U ≤ _)).op (g.app U a) =
      (g.appIso _).hom (X.presheaf.map (homOfLE hle).op a) := by
    have : X.presheaf.map (homOfLE hle).op ≫ (g.appIso _).hom =
        g.app U ≫ Y.presheaf.map (homOfLE (inf_le_right : W ⊓ g ⁻¹ᵁ U ≤ _)).op := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
      rfl
    exact congr($this a).symm
  rw [Scheme.Hom.germ_stalkMap_apply,
    ← Y.presheaf.germ_res_apply (homOfLE (inf_le_right : W ⊓ g ⁻¹ᵁ U ≤ _)) y hy,
    ← (F.restrict g).presheaf.germ_res_apply (homOfLE (inf_le_left : W ⊓ g ⁻¹ᵁ U ≤ _)) y hy,
    ← germ_smul, restrictStalkAddEquiv_germ, restrictStalkAddEquiv_germ,
    ← X.presheaf.germ_res_apply (homOfLE hle) (g y) ⟨y, hy, rfl⟩, key]
  refine Eq.trans ?_ (germ_smul F (U := g ''ᵁ (W ⊓ g ⁻¹ᵁ U)) (g y) ⟨y, hy, rfl⟩ _ _)
  congr 1
  refine (F.smul_restrictAppIso_hom_apply g _ _ _).trans ?_
  rw [Iso.hom_inv_id_apply]

theorem support_restrict {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    support (F.restrict g) = g ⁻¹' support F :=
  Set.ext fun y ↦ (restrictStalkAddEquiv F g y).toEquiv.nontrivial_congr

theorem structureModuleSectionsEquiv_res (h : V ≤ U) (s : Γ(structureModule X, U)) :
    structureModuleSectionsEquiv V ((structureModule X).presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (structureModuleSectionsEquiv U s) := rfl

theorem germ_smul_germ_one (x : X) (hx : x ∈ U) (s : Γ(structureModule X, U)) :
    X.presheaf.germ U x hx (structureModuleSectionsEquiv U s) •
      (structureModule X).presheaf.germ ⊤ x trivial ((structureModuleSectionsEquiv ⊤).symm 1) =
      (structureModule X).presheaf.germ U x hx s := by
  rw [← (structureModule X).presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hx, ← germ_smul]
  congr 1
  apply (structureModuleSectionsEquiv U).injective
  rw [map_smul, structureModuleSectionsEquiv_res, LinearEquiv.apply_symm_apply, map_one,
    smul_eq_mul, mul_one]

def structureModuleStalkEquiv (x : X) :
    ((structureModule X).presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton (X.presheaf.stalk x) _
    ((structureModule X).presheaf.germ ⊤ x trivial
      ((structureModuleSectionsEquiv ⊤).symm 1))) <| by
      refine ⟨(injective_iff_map_eq_zero _).2 fun r hr ↦ ?_, fun t ↦ ?_⟩
      · obtain ⟨U, hx, f, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨s, rfl⟩ := (structureModuleSectionsEquiv U).surjective f
        rw [LinearMap.toSpanSingleton_apply, germ_smul_germ_one] at hr
        obtain ⟨W, hW, i, j, e⟩ := (structureModule X).presheaf.germ_eq x hx hx s 0
          (by rw [hr, map_zero])
        rw [map_zero] at e
        rw [← X.presheaf.germ_res_apply (homOfLE i.le) x hW, ← structureModuleSectionsEquiv_res]
        have e' : (structureModule X).presheaf.map (homOfLE i.le).op s = 0 := e
        rw [e', map_zero, map_zero]
      · obtain ⟨U, hx, s, rfl⟩ := (structureModule X).presheaf.exists_germ_eq t
        exact ⟨_, germ_smul_germ_one x hx s⟩).symm

@[simp]
theorem structureModuleStalkEquiv_germ (x : X) (hx : x ∈ U) (s : Γ(structureModule X, U)) :
    structureModuleStalkEquiv x ((structureModule X).presheaf.germ U x hx s) =
      X.presheaf.germ U x hx (structureModuleSectionsEquiv U s) := by
  rw [structureModuleStalkEquiv, LinearEquiv.symm_apply_eq]
  exact (germ_smul_germ_one x hx s).symm

@[simp]
theorem support_structureModule : support (structureModule X) = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ (structureModuleStalkEquiv x).toEquiv.nontrivial

theorem support_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    support (tilde M) = Module.support R M := by
  refine Set.ext fun x : PrimeSpectrum.Top R ↦ ?_
  have := x.isPrime
  exact (IsLocalizedModule.iso x.asIdeal.primeCompl
    (tilde.toStalk M x).hom).toEquiv.nontrivial_congr.symm

end Support

section Dimension

theorem isIrreducible_of_image {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] {f : S → T}
    (hf : Topology.IsInducing f) {s : Set S} (h : IsIrreducible (f '' s)) : IsIrreducible s := by
  refine ⟨h.nonempty.of_image, fun a b ha hb ⟨x, hx, hxa⟩ ⟨y, hy, hyb⟩ ↦ ?_⟩
  obtain ⟨a, ha', rfl⟩ := hf.isOpen_iff.1 ha
  obtain ⟨b, hb', rfl⟩ := hf.isOpen_iff.1 hb
  obtain ⟨_, ⟨z, hz, rfl⟩, hza⟩ := h.2 a b ha' hb' ⟨_, ⟨x, hx, rfl⟩, hxa⟩ ⟨_, ⟨y, hy, rfl⟩, hyb⟩
  exact ⟨z, hz, hza⟩

theorem topologicalKrullDim_le_of_irreducibleCloseds {T : Type*} [TopologicalSpace T]
    {d : WithBot ℕ∞} (h : ∀ Z : IrreducibleCloseds T, topologicalKrullDim (Z : Set T) ≤ d) :
    topologicalKrullDim T ≤ d := by
  refine iSup_le fun p ↦ le_trans ?_ (h p.last)
  let L : Set T := (p.last : IrreducibleCloseds T)
  have hle (i : Fin (p.length + 1)) : ((p i : IrreducibleCloseds T) : Set T) ⊆ L := p.monotone (Fin.le_last i)
  have him (i : Fin (p.length + 1)) :
      Subtype.val '' ((Subtype.val : L → T) ⁻¹' (p i : IrreducibleCloseds T)) = (p i : IrreducibleCloseds T) := by
    rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 (hle i)]
  let q : LTSeries (IrreducibleCloseds L) := LTSeries.mk p.length
    (fun i ↦ ⟨Subtype.val ⁻¹' ((p i : IrreducibleCloseds T) : Set T),
      isIrreducible_of_image .subtypeVal
      ((him i).symm ▸ (p i).isIrreducible), (p i).isClosed.preimage continuous_subtype_val⟩)
    fun i j hij ↦ by
      refine lt_of_le_of_ne (fun z hz ↦ p.monotone hij.le hz) fun e ↦
        (p.strictMono hij).ne (IrreducibleCloseds.ext ?_)
      rw [← him i, ← him j]
      exact congrArg (fun Z : IrreducibleCloseds L ↦
        Subtype.val '' (Z : Set L)) e
  exact Order.LTSeries.length_le_krullDim q

theorem topologicalKrullDim_mono {T : Type*} [TopologicalSpace T] {s t : Set T} (h : s ⊆ t) :
    topologicalKrullDim s ≤ topologicalKrullDim t :=
  (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

theorem topologicalKrullDim_le_of_isIrreducible {T : Type*} [TopologicalSpace T] {s : Set T}
    {d : WithBot ℕ∞} (h : ∀ Z ⊆ s, IsIrreducible Z → topologicalKrullDim Z ≤ d) :
    topologicalKrullDim s ≤ d := by
  refine topologicalKrullDim_le_of_irreducibleCloseds fun Z ↦ le_trans ?_
    (h (Subtype.val '' (Z : Set s)) (Subtype.coe_image_subset _ _)
      (Z.isIrreducible.image _ continuous_subtype_val.continuousOn))
  exact (Topology.IsEmbedding.subtypeVal.homeomorphImage
    (Z : Set s)).isInducing.topologicalKrullDim_le

theorem topologicalKrullDim_union {T : Type*} [TopologicalSpace T] {s t : Set T}
    (hs : IsClosed s) (ht : IsClosed t) :
    topologicalKrullDim (s ∪ t :) = max (topologicalKrullDim s) (topologicalKrullDim t) := by
  refine le_antisymm (topologicalKrullDim_le_of_isIrreducible fun Z hZ hirr ↦ ?_)
    (max_le (topologicalKrullDim_mono Set.subset_union_left)
      (topologicalKrullDim_mono Set.subset_union_right))
  rcases isPreirreducible_iff_isClosed_union_isClosed.1 hirr.2 s t hs ht hZ with h | h
  · exact (topologicalKrullDim_mono h).trans (le_max_left _ _)
  · exact (topologicalKrullDim_mono h).trans (le_max_right _ _)

theorem topologicalKrullDim_eq_iSup_closure {T : Type*} [TopologicalSpace T] [QuasiSober T]
    {s : Set T} (hs : IsClosed s) :
    topologicalKrullDim s = ⨆ x ∈ s, topologicalKrullDim (closure {x} : Set T) := by
  refine le_antisymm (topologicalKrullDim_le_of_isIrreducible fun Z hZ hirr ↦ ?_)
    (iSup₂_le fun x hx ↦ topologicalKrullDim_mono
      (hs.closure_subset_iff.2 (Set.singleton_subset_iff.2 hx)))
  have hx := hirr.isGenericPoint_genericPoint_closure
  refine le_iSup₂_of_le hirr.genericPoint (hs.closure_subset_iff.2 hZ hx.mem)
    (topologicalKrullDim_mono ?_)
  rw [hx.def]
  exact subset_closure

theorem topologicalKrullDim_eq_bot_iff {T : Type*} [TopologicalSpace T] :
    topologicalKrullDim T = ⊥ ↔ IsEmpty T := by
  rw [topologicalKrullDim, Order.krullDim_eq_bot_iff]
  exact ⟨fun h ↦ ⟨fun x ↦ h.false ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩,
    fun h ↦ ⟨fun Z ↦ h.false Z.isIrreducible.nonempty.some⟩⟩

variable (F) in

def suppDim : WithBot ℕ∞ := topologicalKrullDim (support F)

theorem suppDim_eq_bot_iff : suppDim F = ⊥ ↔ IsZero F := by
  rw [suppDim, topologicalKrullDim_eq_bot_iff, Set.isEmpty_coe_sort, support_eq_empty_iff]

theorem suppDim_lt_zero_iff : suppDim F < 0 ↔ IsZero F := by
  rw [← suppDim_eq_bot_iff]
  exact WithBot.lt_coe_bot

variable (F) in

theorem suppDim_le : suppDim F ≤ topologicalKrullDim X :=
  topologicalKrullDim_subspace_le X _

theorem suppDim_le_of_support_subset (h : support F ⊆ support G) : suppDim F ≤ suppDim G :=
  topologicalKrullDim_mono h

theorem suppDim_le_of_mono (φ : F ⟶ G) [Mono φ] : suppDim F ≤ suppDim G :=
  suppDim_le_of_support_subset (support_subset_of_mono φ)

theorem suppDim_le_of_epi (φ : F ⟶ G) [Epi φ] : suppDim G ≤ suppDim F :=
  suppDim_le_of_support_subset (support_subset_of_epi φ)

theorem suppDim_eq_of_iso (e : F ≅ G) : suppDim F = suppDim G := by
  rw [suppDim, suppDim, support_eq_of_iso e]

theorem suppDim_eq_max_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteQC S.X₁] [IsFiniteQC S.X₃] : suppDim S.X₂ = max (suppDim S.X₁) (suppDim S.X₃) := by
  rw [suppDim, support_eq_union_of_shortExact hS]
  exact topologicalKrullDim_union (isClosed_support _) (isClosed_support _)

variable (F) in

theorem suppDim_eq_iSup_closure [IsFiniteQC F] :
    suppDim F = ⨆ x ∈ support F, topologicalKrullDim (closure {x} : Set X) :=
  topologicalKrullDim_eq_iSup_closure (isClosed_support F)

@[simp]
theorem suppDim_structureModule : suppDim (structureModule X) = topologicalKrullDim X := by
  rw [suppDim, support_structureModule]
  exact (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq

theorem suppDim_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R) [Module.Finite R M] :
    suppDim (tilde M) = Module.supportDim R M := by
  rw [suppDim, support_tilde, Module.supportDim, Module.support_eq_zeroLocus,
    Order.krullDim_eq_of_orderIso (PrimeSpectrum.zeroLocusEquivIrreducibleCloseds _),
    Order.krullDim_orderDual]
  rfl

end Dimension

section Associated

variable (F) in

def assPoints : Set X :=
  {x | maximalIdeal (X.presheaf.stalk x) ∈
    associatedPrimes (X.presheaf.stalk x) (F.presheaf.stalk x :)}

theorem mem_assPoints_iff {x : X} : x ∈ assPoints F ↔
    IsAssociatedPrime (maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x :) := Iff.rfl

theorem mem_assPoints_iff_exists_pow {x : X} :
    x ∈ assPoints F ↔ ∃ t : (F.presheaf.stalk x :),
      ∀ r : X.presheaf.stalk x, (∃ n : ℕ, r ^ n • t = 0) ↔ ¬ IsUnit r := by
  rw [mem_assPoints_iff, IsAssociatedPrime, Submodule.isAssociatedPrime_def,
    and_iff_right (maximalIdeal.isMaximal _).isPrime]
  refine exists_congr fun t ↦ ?_
  simp only [Ideal.ext_iff, Ideal.mem_radical_iff, Submodule.mem_colon_singleton, Submodule.mem_bot]
  exact forall_congr' fun _ ↦ Iff.comm

theorem assPoints_restrict {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    assPoints (F.restrict g) = g ⁻¹' assPoints F := by
  ext y
  rw [Set.mem_preimage, mem_assPoints_iff_exists_pow, mem_assPoints_iff_exists_pow]
  refine (restrictStalkAddEquiv F g y).toEquiv.exists_congr fun t ↦ ?_
  rw [(ConcreteCategory.bijective_of_isIso (g.stalkMap y)).2.forall]
  refine forall_congr' fun r ↦ iff_congr (exists_congr fun n ↦ ?_)
    (not_congr (isUnit_map_iff (g.stalkMap y).hom r))
  rw [← map_pow, ← (restrictStalkAddEquiv F g y).map_eq_zero_iff, restrictStalkAddEquiv_smul]
  rfl

theorem mem_assPoints_iff_exists [IsLocallyNoetherian X] {x : X} :
    x ∈ assPoints F ↔ ∃ t : (F.presheaf.stalk x :),
      ∀ r : X.presheaf.stalk x, r • t = 0 ↔ r ∈ maximalIdeal (X.presheaf.stalk x) := by
  rw [mem_assPoints_iff, isAssociatedPrime_iff,
    and_iff_right (maximalIdeal.isMaximal _).isPrime]
  refine exists_congr fun t ↦ ?_
  simp only [Ideal.ext_iff, Submodule.mem_colon_singleton, Submodule.mem_bot]
  exact forall_congr' fun _ ↦ Iff.comm

variable (F) in

theorem assPoints_subset_support : assPoints F ⊆ support F := fun _ hx ↦ by
  by_contra h
  have := notMem_support_iff.1 h
  exact not_isAssociatedPrime_of_subsingleton hx

theorem assPoints_subset_of_mono (φ : F ⟶ G) [Mono φ] : assPoints F ⊆ assPoints G :=
  fun x hx ↦ associatedPrimes.subset_of_injective (stalkLinear_injective φ x) hx

theorem assPoints_eq_of_iso (e : F ≅ G) : assPoints F = assPoints G :=
  (assPoints_subset_of_mono e.hom).antisymm (assPoints_subset_of_mono e.inv)

theorem assPoints_subset_union_of_exact {S : ShortComplex X.Modules} (hS : S.Exact) [Mono S.f] :
    assPoints S.X₂ ⊆ assPoints S.X₁ ∪ assPoints S.X₃ := fun x hx ↦
  associatedPrimes.subset_union_of_exact (stalkLinear_injective S.f x)
    ((exact_iff_stalkLinear S).1 hS x) hx

variable [IsLocallyNoetherian X]

variable (F) in

theorem mem_associatedPrimes_stalk_iff [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U)
    (Q : Ideal (X.presheaf.stalk (x : X))) :
    Q ∈ associatedPrimes (X.presheaf.stalk (x : X)) (F.presheaf.stalk (x : X) :) ↔
      Q.comap (algebraMap Γ(X, U) _) ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  have := hU.isLocalization_stalk x
  have := isLocalizedModule_germLinear F hU x
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  rw [← Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    (hU.primeIdealOf x).asIdeal.primeCompl _ (germLinear F x)]
  rfl

theorem mem_assPoints_iff_primeIdealOf [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    (x : X) ∈ assPoints F ↔ (hU.primeIdealOf x).asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  have := hU.isLocalization_stalk x
  rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (x : X))
    (hU.primeIdealOf x).asIdeal]
  exact mem_associatedPrimes_stalk_iff F hU x _

theorem pointOfPrime_mem_assPoints_iff [F.IsQuasicoherent] (hU : IsAffineOpen U)
    (P : PrimeSpectrum Γ(X, U)) :
    (pointOfPrime hU P : X) ∈ assPoints F ↔ P.asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  rw [mem_assPoints_iff_primeIdealOf hU, primeIdealOf_pointOfPrime]

variable (F) in

theorem finite_assPoints_inter_affine [IsFiniteQC F] (hU : IsAffineOpen U) :
    (assPoints F ∩ U).Finite := by
  have := finite_sections F hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have h : (PrimeSpectrum.asIdeal ⁻¹' associatedPrimes Γ(X, U) Γ(F, U)).Finite :=
    (associatedPrimes.finite Γ(X, U) Γ(F, U)).preimage fun _ _ _ _ ↦ PrimeSpectrum.ext
  refine (h.image fun P ↦ (pointOfPrime hU P : X)).subset fun x hx ↦
    ⟨hU.primeIdealOf ⟨x, hx.2⟩, (mem_assPoints_iff_primeIdealOf hU ⟨x, hx.2⟩).1 hx.1, ?_⟩
  simp only [pointOfPrime_primeIdealOf]

variable (F) in

theorem finite_assPoints_inter_of_isCompact [IsFiniteQC F] {K : Set X} (hK : IsCompact K) :
    (assPoints F ∩ K).Finite := by
  choose W hW hxW using exists_affine_mem (X := X)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x ↦ (W x : Set X)) (fun x ↦ (W x).2)
    fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxW x⟩
  refine (t.finite_toSet.biUnion fun x _ ↦ finite_assPoints_inter_affine F (hW x)).subset
    fun y hy ↦ ?_
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy.2)
  exact Set.mem_iUnion₂.2 ⟨x, hx, hy.1, hyx⟩

variable (F) in

theorem finite_assPoints [CompactSpace X] [IsFiniteQC F] : (assPoints F).Finite := by
  simpa using finite_assPoints_inter_of_isCompact F isCompact_univ

theorem exists_mem_assPoints_specializes [F.IsQuasicoherent] {x : X} (hx : x ∈ support F) :
    ∃ y ∈ assPoints F, y ⤳ x := by
  obtain ⟨U, hU, hxU⟩ := exists_affine_mem x
  obtain ⟨x, rfl⟩ : ∃ x' : U, x' = x := ⟨⟨x, hxU⟩, rfl⟩
  have := mem_support_iff.1 hx
  have := hU.isLocalization_stalk x
  obtain ⟨Q, hQ⟩ :=
    associatedPrimes.nonempty (X.presheaf.stalk (x : X)) (F.presheaf.stalk (x : X) :)
  have hQ' := (mem_associatedPrimes_stalk_iff F hU x Q).1 hQ
  let P : PrimeSpectrum Γ(X, U) := ⟨_, hQ'.isPrime⟩
  refine ⟨pointOfPrime hU P, (pointOfPrime_mem_assPoints_iff hU P).2 hQ', ?_⟩
  have hle : P ≤ hU.primeIdealOf x := by
    change P.asIdeal ≤ (hU.primeIdealOf x).asIdeal
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (x : X))
      (hU.primeIdealOf x).asIdeal]
    exact Ideal.comap_mono (le_maximalIdeal hQ.isPrime.ne_top)
  have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
  rwa [hU.fromSpec_primeIdealOf] at this

theorem mem_assPoints_of_forall_specializes [F.IsQuasicoherent] {x : X} (hx : x ∈ support F)
    (h : ∀ y ∈ support F, y ⤳ x → y = x) : x ∈ assPoints F := by
  obtain ⟨y, hy, hyx⟩ := exists_mem_assPoints_specializes hx
  exact h y (assPoints_subset_support F hy) hyx ▸ hy

variable (F) in

theorem closure_assPoints [IsFiniteQC F] : closure (assPoints F) = support F := by
  refine ((isClosed_support F).closure_subset_iff.2 (assPoints_subset_support F)).antisymm
    fun x hx ↦ ?_
  obtain ⟨y, hy, hyx⟩ := exists_mem_assPoints_specializes hx
  exact hyx.mem_closed isClosed_closure (subset_closure hy)

theorem assPoints_eq_empty_iff [F.IsQuasicoherent] : assPoints F = ∅ ↔ IsZero F := by
  rw [← support_eq_empty_iff]
  refine ⟨fun h ↦ Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_,
    fun h ↦ Set.subset_eq_empty (assPoints_subset_support F) h⟩
  obtain ⟨y, hy, -⟩ := exists_mem_assPoints_specializes hx
  exact Set.eq_empty_iff_forall_notMem.1 h y hy

theorem section_eq_zero_of_germ_assPoints [F.IsQuasicoherent] (s : Γ(F, U))
    (h : ∀ x ∈ assPoints F, ∀ hx : x ∈ U, F.presheaf.germ U x hx s = 0) : s = 0 := by
  refine section_eq_zero_of_germ s fun x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := exists_affine_mem_le x hx
  rw [← F.presheaf.germ_res_apply (homOfLE hVU) x hxV]
  suffices F.presheaf.map (homOfLE hVU).op s = 0 by rw [this, map_zero]
  by_contra hs
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing Γ(X, V) _ hs
  have := hP.isPrime
  have := isLocalizedModule_germLinear_pointOfPrime F hV P
  let y := pointOfPrime hV ⟨P, hP.isPrime⟩
  have hy : germLinear F y (F.presheaf.map (homOfLE hVU).op s) = 0 := by
    rw [germLinear_apply, F.presheaf.germ_res_apply]
    exact h y ((pointOfPrime_mem_assPoints_iff hV _).2 hP) _
  obtain ⟨r, hr⟩ := (IsLocalizedModule.eq_zero_iff P.primeCompl (germLinear F y)).1 hy
  exact r.2 (hle (Submodule.mem_colon_singleton.2 hr))

theorem isSMulRegular_sections_iff [F.IsQuasicoherent] (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsSMulRegular Γ(F, U) f ↔ assPoints F ∩ U ⊆ X.basicOpen f := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have h : f ∈ (⋃ p ∈ associatedPrimes Γ(X, U) Γ(F, U), (p : Set Γ(X, U))) ↔
      ¬ IsSMulRegular Γ(F, U) f := by
    rw [biUnion_associatedPrimes_eq_compl_regular]; rfl
  rw [← not_iff_not, ← h, Set.mem_iUnion₂, Set.not_subset]
  constructor
  · rintro ⟨P, hP, hf⟩
    let y := pointOfPrime hU ⟨P, hP.isPrime⟩
    refine ⟨y, ⟨(pointOfPrime_mem_assPoints_iff hU _).2 hP, y.2⟩, fun hy ↦ ?_⟩
    have := (mem_primeCompl_primeIdealOf_iff hU y f).2 hy
    rw [Ideal.mem_primeCompl_iff, primeIdealOf_pointOfPrime] at this
    exact this hf
  · rintro ⟨x, ⟨hx, hxU⟩, hf⟩
    refine ⟨_, (mem_assPoints_iff_primeIdealOf hU ⟨x, hxU⟩).1 hx, ?_⟩
    by_contra hf'
    exact hf ((mem_primeCompl_primeIdealOf_iff hU ⟨x, hxU⟩ f).1 hf')

theorem isSMulRegular_stalk_iff [F.IsQuasicoherent] (f : Γ(X, U)) :
    (∀ (x : X) (hx : x ∈ U), IsSMulRegular (F.presheaf.stalk x :) (X.presheaf.germ U x hx f)) ↔
      assPoints F ∩ U ⊆ X.basicOpen f := by
  constructor
  · rintro h x ⟨hx, hxU⟩
    obtain ⟨t, ht⟩ := mem_assPoints_iff_exists.1 hx
    by_contra hf
    have hm : X.presheaf.germ U x hxU f ∈ maximalIdeal (X.presheaf.stalk x) :=
      fun hu ↦ hf ((X.mem_basicOpen f x hxU).2 hu)
    have ht0 : t = 0 := (h x hxU).right_eq_zero_of_smul ((ht _).2 hm)
    exact (ht 1).1 (by rw [ht0, smul_zero]) isUnit_one
  · intro h x hx
    obtain ⟨V, hV, hxV, hVU⟩ := exists_affine_mem_le x hx
    obtain ⟨x, rfl⟩ : ∃ x' : V, x' = x := ⟨⟨x, hxV⟩, rfl⟩
    have hreg := (isSMulRegular_sections_iff (F := F) hV
      (X.presheaf.map (homOfLE hVU).op f)).2 fun y hy ↦ by
        rw [Scheme.basicOpen_res]
        exact ⟨hy.2, h ⟨hy.1, hVU hy.2⟩⟩
    have := hV.isLocalization_stalk x
    have := isLocalizedModule_germLinear F hV x
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV]
    exact IsSMulRegular.of_isLocalizedModule (X.presheaf.stalk (x : X))
      (hV.primeIdealOf x).asIdeal.primeCompl (germLinear F x) hreg

omit [IsLocallyNoetherian X] in

theorem assPoints_tilde {R : CommRingCat.{u}} [IsNoetherianRing R] (M : ModuleCat.{u} R) :
    assPoints (tilde M) = PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R M := by
  refine Set.ext fun x : Spec R ↦ ?_
  have hb := algebraMap_Spec_top_bijective (R := R)
  have : IsLocalization (Submonoid.powers (1 : R)) Γ(Spec R, ⊤) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one hb
  have : IsLocalizedModule (Submonoid.powers (1 : R)) (tildeTopEquiv M).toLinearMap :=
    IsLocalizedModule.Away.mk_of_addCommGroup (by rw [map_one]; exact isUnit_one)
      (fun s ↦ ⟨0, (tildeTopEquiv M).symm s, by simp⟩) fun t ht ↦ ⟨0, by simpa using ht⟩
  refine (mem_assPoints_iff_primeIdealOf (isAffineOpen_top (Spec R)) ⟨x, trivial⟩).trans ?_
  rw [← Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    (Submonoid.powers (1 : R)) _ (tildeTopEquiv M).toLinearMap]
  have e : ((isAffineOpen_top (Spec R)).primeIdealOf ⟨x, trivial⟩).asIdeal.comap
      (algebraMap R Γ(Spec R, ⊤)) = x.asIdeal := by
    ext r
    rw [Ideal.mem_comap, ← not_iff_not]
    refine (mem_primeCompl_primeIdealOf_iff (isAffineOpen_top (Spec R)) ⟨x, trivial⟩ _).trans ?_
    have : (Spec R).basicOpen (algebraMap R Γ(Spec R, ⊤) r) = PrimeSpectrum.basicOpen r :=
      basicOpen_eq_of_affine r
    rw [this]
    rfl
  rw [Set.mem_preimage, e]
  rfl

end Associated

section Fibre

instance residueFieldAlgebra (x : X) : Algebra (X.presheaf.stalk x) (X.residueField x) :=
  inferInstanceAs (Algebra (X.presheaf.stalk x) (ResidueField (X.presheaf.stalk x)))

theorem algebraMap_residueField (x : X) :
    algebraMap (X.presheaf.stalk x) (X.residueField x) = (X.residue x).hom := rfl

instance residueFieldAlgebraSections (x : U) : Algebra Γ(X, U) (X.residueField (x : X)) :=
  (X.evaluation U x x.2).hom.toAlgebra

theorem algebraMap_sections_residueField (x : U) :
    algebraMap Γ(X, U) (X.residueField (x : X)) = (X.evaluation U x x.2).hom := rfl

instance isScalarTower_residueField (x : U) :
    IsScalarTower Γ(X, U) (X.presheaf.stalk (x : X)) (X.residueField (x : X)) :=
  .of_algebraMap_eq fun _ ↦ rfl

variable (F) in

abbrev fibre (x : X) : Type u := X.residueField x ⊗[X.presheaf.stalk x] (F.presheaf.stalk x :)

variable (F) in

def fibreMk (x : X) : (F.presheaf.stalk x :) →ₗ[X.presheaf.stalk x] fibre F x :=
  TensorProduct.mk _ _ _ 1

theorem fibreMk_apply (x : X) (t : (F.presheaf.stalk x :)) : fibreMk F x t = 1 ⊗ₜ t := rfl

variable (F) in

theorem fibreMk_surjective (x : X) : Function.Surjective (fibreMk F x) :=
  TensorProduct.mk_surjective _ _ _ (X.residue_surjective x)

variable (F) in

def fibreEquivQuotient (x : X) : fibre F x ≃ₗ[X.presheaf.stalk x]
    ((F.presheaf.stalk x :) ⧸ (maximalIdeal (X.presheaf.stalk x) • ⊤ :
      Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :))) :=
  quotTensorEquivQuotSMul _ (maximalIdeal (X.presheaf.stalk x))

@[simp]
theorem fibreEquivQuotient_fibreMk (x : X) (t : (F.presheaf.stalk x :)) :
    fibreEquivQuotient F x (fibreMk F x t) = Submodule.Quotient.mk t :=
  quotTensorEquivQuotSMul_mk_one_tmul _ t

theorem fibreMk_eq_zero_iff (x : X) (t : (F.presheaf.stalk x :)) :
    fibreMk F x t = 0 ↔ t ∈ (maximalIdeal (X.presheaf.stalk x) • ⊤ :
      Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) := by
  rw [← (fibreEquivQuotient F x).map_eq_zero_iff, fibreEquivQuotient_fibreMk,
    Submodule.Quotient.mk_eq_zero]

variable (F) in

def fibreEval (x : U) : Γ(F, U) →ₗ[Γ(X, U)] fibre F x :=
  (fibreMk F x).restrictScalars Γ(X, U) ∘ₗ germLinear F x

theorem fibreEval_apply (x : U) (s : Γ(F, U)) :
    fibreEval F x s = fibreMk F x (F.presheaf.germ U x x.2 s) := rfl

theorem fibreEval_smul (x : U) (f : Γ(X, U)) (s : Γ(F, U)) :
    fibreEval F x (f • s) = X.evaluation U x x.2 f • fibreEval F x s := by
  rw [map_smul, ← algebraMap_smul (X.residueField (x : X))]; rfl

theorem fibreEval_res (h : V ≤ U) (x : V) (s : Γ(F, U)) :
    fibreEval F x (F.presheaf.map (homOfLE h).op s) = fibreEval F (⟨x, h x.2⟩ : U) s := by
  rw [fibreEval_apply, fibreEval_apply, F.presheaf.germ_res_apply]

variable (F) in

theorem isBaseChange_fibreEval [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    IsBaseChange (X.residueField (x : X)) (fibreEval F x) :=
  (isBaseChange_germLinear F hU x).comp (TensorProduct.isBaseChange _ _ _)

def fibreMap (φ : F ⟶ G) (x : X) : fibre F x →ₗ[X.residueField x] fibre G x :=
  (stalkLinear φ x).baseChange (X.residueField x)

@[simp]
theorem fibreMap_fibreMk (φ : F ⟶ G) (x : X) (t : (F.presheaf.stalk x :)) :
    fibreMap φ x (fibreMk F x t) = fibreMk G x (stalkLinear φ x t) := rfl

@[simp]
theorem fibreMap_fibreEval (φ : F ⟶ G) (x : U) (s : Γ(F, U)) :
    fibreMap φ x (fibreEval F x s) = fibreEval G x (φ.app U s) := by
  rw [fibreEval_apply, fibreEval_apply, fibreMap_fibreMk, stalkLinear_germ]

@[simp]
theorem fibreMap_id (x : X) : fibreMap (𝟙 F) x = LinearMap.id := by
  rw [fibreMap, stalkLinear_id, LinearMap.baseChange_id]

@[simp]
theorem fibreMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) (x : X) :
    fibreMap (φ ≫ ψ) x = fibreMap ψ x ∘ₗ fibreMap φ x := by
  rw [fibreMap, stalkLinear_comp, LinearMap.baseChange_comp]; rfl

@[simp]
theorem fibreMap_add (φ ψ : F ⟶ G) (x : X) :
    fibreMap (φ + ψ) x = fibreMap φ x + fibreMap ψ x := by
  rw [fibreMap, stalkLinear_add, LinearMap.baseChange_add]; rfl

@[simp]
theorem fibreMap_zero (x : X) : fibreMap (0 : F ⟶ G) x = 0 := by
  rw [fibreMap, stalkLinear_zero, LinearMap.baseChange_zero]

def fibreEquiv (e : F ≅ G) (x : X) : fibre F x ≃ₗ[X.residueField x] fibre G x :=
  (stalkLinearEquiv e x).baseChange _ (X.residueField x) _ _

@[simp]
theorem fibreEquiv_apply (e : F ≅ G) (x : X) (t : fibre F x) :
    fibreEquiv e x t = fibreMap e.hom x t := rfl

theorem fibreMap_surjective (φ : F ⟶ G) [Epi φ] (x : X) : Function.Surjective (fibreMap φ x) :=
  LinearMap.lTensor_surjective _ (stalkLinear_surjective φ x)

theorem fibreMap_exact {S : ShortComplex X.Modules} (hS : S.Exact) [Epi S.g] (x : X) :
    Function.Exact (fibreMap S.f x) (fibreMap S.g x) :=
  lTensor_exact _ ((exact_iff_stalkLinear S).1 hS x) (stalkLinear_surjective S.g x)

instance finite_fibre [IsFiniteQC F] (x : X) : Module.Finite (X.residueField x) (fibre F x) :=
  inferInstance

theorem nontrivial_fibre_iff [IsFiniteQC F] {x : X} : Nontrivial (fibre F x) ↔ x ∈ support F := by
  rw [← not_iff_not, not_nontrivial_iff_subsingleton, notMem_support_iff]
  exact IsLocalRing.subsingleton_tensorProduct

theorem map_fibreMk_eq_top_iff [IsFiniteQC F] (x : X)
    (N : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) :
    N.map (fibreMk F x) = ⊤ ↔ N = ⊤ :=
  IsLocalRing.map_tensorProduct_mk_eq_top

theorem span_fibreMk_eq_top_iff [IsFiniteQC F] (x : X) (s : Set (F.presheaf.stalk x :)) :
    Submodule.span (X.residueField x) (fibreMk F x '' s) = ⊤ ↔
      Submodule.span (X.presheaf.stalk x) s = ⊤ := by
  rw [← map_fibreMk_eq_top_iff, Submodule.map_span,
    ← Submodule.restrictScalars_span _ (X.residueField x) (X.residue_surjective x),
    Submodule.restrictScalars_eq_top_iff]

theorem fibreMap_surjective_iff (φ : F ⟶ G) [IsFiniteQC G] (x : X) :
    Function.Surjective (fibreMap φ x) ↔ Function.Surjective (stalkLinear φ x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ LinearMap.lTensor_surjective _ h⟩
  rw [← LinearMap.range_eq_top, ← map_fibreMk_eq_top_iff, eq_top_iff]
  intro v _
  obtain ⟨w, rfl⟩ := h v
  obtain ⟨t, rfl⟩ := fibreMk_surjective F x w
  exact ⟨_, ⟨t, rfl⟩, rfl⟩

theorem epi_iff_fibreMap_surjective (φ : F ⟶ G) [IsFiniteQC G] :
    Epi φ ↔ ∀ x : X, Function.Surjective (fibreMap φ x) := by
  simp only [epi_iff_stalkLinear_surjective, fibreMap_surjective_iff]

def structureModuleFibreEquiv (x : X) :
    fibre (structureModule X) x ≃ₗ[X.residueField x] X.residueField x :=
  ((structureModuleStalkEquiv x).baseChange _ (X.residueField x) _ _).trans
    (AlgebraTensorModule.rid _ _ _)

@[simp]
theorem structureModuleFibreEquiv_fibreEval (x : U) (s : Γ(structureModule X, U)) :
    structureModuleFibreEquiv (x : X) (fibreEval (structureModule X) x s) =
      X.evaluation U x x.2 (structureModuleSectionsEquiv U s) := by
  rw [fibreEval_apply, fibreMk_apply, structureModuleFibreEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, structureModuleStalkEquiv_germ, AlgebraTensorModule.rid_tmul,
    ← Algebra.algebraMap_eq_smul_one]
  rfl

end Fibre

section Flat

variable {R : Type*} [CommRing R] (ρ : R →+* Γ(X, ⊤))

variable (U) in

def baseHom : R →+* Γ(X, U) := (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom.comp ρ

theorem baseHom_apply (r : R) :
    baseHom U ρ r = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (ρ r) := rfl

@[simp]
theorem res_baseHom (h : V ≤ U) (r : R) :
    X.presheaf.map (homOfLE h).op (baseHom U ρ r) = baseHom V ρ r :=
  res_res_ring le_top h (ρ r)

@[simp]
theorem baseHom_top : baseHom ⊤ ρ = ρ := RingHom.ext fun r ↦ res_self_ring le_top (ρ r)

@[simp]
theorem germ_baseHom (x : X) (hx : x ∈ U) (r : R) :
    X.presheaf.germ U x hx (baseHom U ρ r) = X.presheaf.germ ⊤ x trivial (ρ r) :=
  X.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hx (ρ r)

variable (F U) in

abbrev baseModule : Module R Γ(F, U) := Module.compHom _ (baseHom U ρ)

variable (F) in

abbrev baseModuleStalk (x : X) : Module R (F.presheaf.stalk x :) :=
  Module.compHom _ ((X.presheaf.germ ⊤ x trivial).hom.comp ρ)

def structureRingHom {R : CommRingCat.{u}} (f : X ⟶ Spec R) : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom

variable (F) in

def IsFlatOver : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    letI := baseModule F U ρ
    Module.Flat R Γ(F, U)

variable {ρ}

theorem IsFlatOver.flat (h : IsFlatOver F ρ) (hU : IsAffineOpen U) [m : Module R Γ(F, U)]
    (hm : ∀ (r : R) (s : Γ(F, U)), r • s = baseHom U ρ r • s) : Module.Flat R Γ(F, U) := by
  obtain rfl : m = baseModule F U ρ := Module.ext' _ _ hm
  exact h U hU

theorem flat_of_isLocalizedModule_of_flat {A S M N : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M] [AddCommGroup N] [Module A N]
    [Module S N] [IsScalarTower A S N] (T : Submonoid S) (f : M →ₗ[S] N) [IsLocalizedModule T f]
    [h : Module.Flat A M] : Module.Flat A N := by
  rw [Module.Flat.iff_lTensor_injectiveₛ] at h ⊢
  intro P _ _ Q
  have := IsLocalizedModule.map_injective T (AlgebraTensorModule.rTensor A Q f)
    (AlgebraTensorModule.rTensor A P f) (AlgebraTensorModule.lTensor S M Q.subtype) (h Q)
  rw [IsLocalizedModule.map_lTensor] at this
  exact this

variable (F ρ) in

theorem flat_sections_iff_stalk [F.IsQuasicoherent] (hU : IsAffineOpen U) :
    (letI := baseModule F U ρ
     Module.Flat R Γ(F, U)) ↔ ∀ x ∈ U,
      letI := baseModuleStalk F ρ x
      Module.Flat R (F.presheaf.stalk x :) := by
  letI := baseModule F U ρ
  letI := (baseHom U ρ).toAlgebra
  haveI : IsScalarTower R Γ(X, U) Γ(F, U) := .of_algebraMap_smul fun _ _ ↦ rfl
  have hst (x : U) : letI := baseModuleStalk F ρ x
      IsScalarTower R Γ(X, U) (F.presheaf.stalk (x : X) :) :=
    letI := baseModuleStalk F ρ x
    .of_algebraMap_smul fun r t ↦ congrArg (· • t) (germ_baseHom ρ x x.2 r)
  constructor
  · intro h x hx
    obtain ⟨x, rfl⟩ : ∃ x' : U, x' = x := ⟨⟨x, hx⟩, rfl⟩
    letI := baseModuleStalk F ρ x
    have := hst x
    have := isLocalizedModule_germLinear F hU x
    exact flat_of_isLocalizedModule_of_flat (hU.primeIdealOf x).asIdeal.primeCompl
      (germLinear F x)
  · intro h
    exact @Module.flat_of_isLocalized_maximal R Γ(X, U) _ _ _ Γ(F, U) _ _ _ _
      (fun P hP ↦ (F.presheaf.stalk (pointOfPrime hU ⟨P, hP.isPrime⟩ : X) :)) _
      (fun P hP ↦ baseModuleStalk F ρ _) _ (fun P hP ↦ hst _)
      (fun P hP ↦ germLinear F (pointOfPrime hU ⟨P, hP.isPrime⟩))
      (fun P hP ↦ isLocalizedModule_germLinear_pointOfPrime F hU P)
      fun P hP ↦ h _ (pointOfPrime hU ⟨P, hP.isPrime⟩).2

theorem isFlatOver_iff_stalk [F.IsQuasicoherent] :
    IsFlatOver F ρ ↔ ∀ x : X,
      letI := baseModuleStalk F ρ x
      Module.Flat R (F.presheaf.stalk x :) := by
  refine ⟨fun h x ↦ ?_, fun h U hU ↦ (flat_sections_iff_stalk F ρ hU).2 fun x _ ↦ h x⟩
  obtain ⟨U, hU, hx⟩ := exists_affine_mem x
  exact (flat_sections_iff_stalk F ρ hU).1 (h U hU) x hx

theorem IsFlatOver.of_forall_exists_affine [F.IsQuasicoherent]
    (h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      letI := baseModule F U ρ
      Module.Flat R Γ(F, U)) : IsFlatOver F ρ :=
  isFlatOver_iff_stalk.2 fun x ↦
    have ⟨_, hU, hx, hf⟩ := h x
    (flat_sections_iff_stalk F ρ hU).1 hf x hx

theorem isFlatOver_iff_affineCover [F.IsQuasicoherent] {ι : Type*} (𝒰 : ι → X.Opens)
    (hcov : IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i)) :
    IsFlatOver F ρ ↔ ∀ i,
      letI := baseModule F (𝒰 i) ρ
      Module.Flat R Γ(F, 𝒰 i) :=
  ⟨fun h i ↦ h _ (haff i), fun h ↦ .of_forall_exists_affine fun x ↦
    have ⟨i, hi⟩ := hcov.exists_mem x
    ⟨𝒰 i, haff i, hi, h i⟩⟩

variable (ρ) in

def sectionsBaseLinear (φ : F ⟶ G) (U : X.Opens) :
    letI := baseModule F U ρ
    letI := baseModule G U ρ
    Γ(F, U) →ₗ[R] Γ(G, U) :=
  letI := baseModule F U ρ
  letI := baseModule G U ρ
  { toFun := φ.app U
    map_add' := map_add _
    map_smul' := fun r s ↦ φ.app_smul (baseHom U ρ r) s }

@[simp]
theorem sectionsBaseLinear_apply (φ : F ⟶ G) (s : Γ(F, U)) :
    sectionsBaseLinear ρ φ U s = φ.app U s := rfl

theorem IsFlatOver.of_sum_eq_id {ι : Type*} [Fintype ι] {A : ι → X.Modules} (p : ∀ i, F ⟶ A i)
    (q : ∀ i, A i ⟶ F) (h : ∑ i, p i ≫ q i = 𝟙 F) (hA : ∀ i, IsFlatOver (A i) ρ) :
    IsFlatOver F ρ := by
  classical
  intro U hU
  letI := baseModule F U ρ
  letI (i : ι) := baseModule (A i) U ρ
  haveI (i : ι) : Module.Flat R Γ(A i, U) := hA i U hU
  haveI : Module.Flat R (∀ i, Γ(A i, U)) :=
    .of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι fun i ↦ Γ(A i, U)).symm
  refine .of_retract (LinearMap.pi fun i ↦ sectionsBaseLinear ρ (p i) U)
    (LinearMap.lsum R (fun i ↦ Γ(A i, U)) ℕ fun i ↦ sectionsBaseLinear ρ (q i) U) ?_
  ext s
  simpa using sum_app_app p q h s

theorem IsFlatOver.of_iso (h : IsFlatOver F ρ) (e : F ≅ G) : IsFlatOver G ρ :=
  .of_sum_eq_id (ι := Unit) (A := fun _ ↦ F) (fun _ ↦ e.inv) (fun _ ↦ e.hom) (by simp) fun _ ↦ h

theorem IsFlatOver.biprod (hF : IsFlatOver F ρ) (hG : IsFlatOver G ρ) : IsFlatOver (F ⊞ G) ρ :=
  .of_sum_eq_id (ι := Bool) (A := fun b ↦ b.casesOn F G)
    (fun b ↦ b.casesOn Limits.biprod.fst Limits.biprod.snd)
    (fun b ↦ b.casesOn Limits.biprod.inl Limits.biprod.inr)
    (by rw [Fintype.sum_bool, add_comm]; exact Limits.biprod.total) fun b ↦ b.casesOn hF hG

theorem IsFlatOver.isSMulRegular (h : IsFlatOver F ρ) {r : R} (hr : r ∈ nonZeroDivisors R)
    (U : X.Opens) : IsSMulRegular Γ(F, U) (baseHom U ρ r) := by
  refine .of_right_eq_zero_of_smul fun s hs ↦ section_eq_zero_of_germ s fun x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := exists_affine_mem_le x hx
  letI := baseModule F V ρ
  haveI : Module.Flat R Γ(F, V) := h V hV
  have h0 : r • F.presheaf.map (homOfLE hVU).op s = 0 := by
    change baseHom V ρ r • F.presheaf.map (homOfLE hVU).op s = 0
    rw [← res_baseHom ρ hVU, ← Scheme.Modules.map_smul, hs, map_zero]
  rw [← F.presheaf.germ_res_apply (homOfLE hVU) x hxV,
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hr).right_eq_zero_of_smul h0, map_zero]

theorem IsFlatOver.restrict (h : IsFlatOver F ρ) {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] : IsFlatOver (F.restrict g) (g.appTop.hom.comp ρ) := by
  intro W hW
  letI := baseModule (F.restrict g) W (g.appTop.hom.comp ρ)
  letI := baseModule F (g ''ᵁ W) ρ
  haveI : Module.Flat R Γ(F, g ''ᵁ W) := h _ (hW.image_of_isOpenImmersion g)
  have key (r : R) : (g.appIso W).hom (baseHom (g ''ᵁ W) ρ r) =
      baseHom W (g.appTop.hom.comp ρ) r := by
    have : X.presheaf.map (homOfLE (le_top : g ''ᵁ W ≤ ⊤)).op ≫ (g.appIso W).hom =
        g.appTop ≫ Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
      rfl
    exact congr($this (ρ r))
  let l : Γ(F, g ''ᵁ W) →ₗ[R] Γ(F.restrict g, W) :=
    { toFun := (F.restrictAppIso g W).inv
      map_add' := map_add _
      map_smul' := fun r s ↦ (F.smul_restrictAppIso_inv_apply g W (baseHom _ ρ r) s).trans
        (congrArg (· • (F.restrictAppIso g W).inv s) (key r)) }
  exact .of_linearEquiv (LinearEquiv.ofBijective l
    (ConcreteCategory.bijective_of_isIso (F.restrictAppIso g W).inv)).symm

theorem isFlatOver_of_field {k : Type*} [Field k] (ρ : k →+* Γ(X, ⊤)) : IsFlatOver F ρ :=
  fun U _ ↦ letI := baseModule F U ρ; inferInstance

theorem isFlatOver_structureModule_iff :
    IsFlatOver (structureModule X) ρ ↔ ∀ U : X.Opens, IsAffineOpen U → (baseHom U ρ).Flat :=
  Iff.rfl

theorem isFlatOver_structureModule_iff_flat {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    IsFlatOver (structureModule X) (structureRingHom f) ↔ Flat f := by
  rw [isFlatOver_structureModule_iff, HasRingHomProperty.iff_of_iSup_eq_top (P := @Flat)
    (fun U : X.affineOpens ↦ U) (iSup_affineOpens_eq_top X)]
  have key (U : X.Opens) : (baseHom U (structureRingHom f)).Flat ↔
      (f.appLE ⊤ U le_top).hom.Flat :=
    RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso R).inv (f.appLE ⊤ U le_top)
  exact ⟨fun h U ↦ (key U).1 (h U U.2), fun h U hU ↦ (key U).2 (h ⟨U, hU⟩)⟩

theorem baseHom_structureRingHom {R : CommRingCat.{u}} (f : X ⟶ Spec R) (U : X.Opens) :
    baseHom U (structureRingHom f) = ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ U le_top).hom := rfl

theorem isFlatOver_Spec_iff {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsFlatOver M (Scheme.ΓSpecIso R).inv.hom ↔ Module.Flat R Γ(M, ⊤) :=
  ⟨fun h ↦ h ⊤ (isAffineOpen_top _),
    fun h ↦ .of_forall_exists_affine fun _ ↦ ⟨⊤, isAffineOpen_top _, trivial, h⟩⟩

theorem isFlatOver_tilde_iff {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    IsFlatOver (tilde M) (Scheme.ΓSpecIso R).inv.hom ↔ Module.Flat R M := by
  rw [isFlatOver_Spec_iff]
  exact (Module.Flat.equiv_iff (tildeTopEquiv M)).symm

@[simp]
theorem structureRingHom_id {R : CommRingCat.{u}} :
    structureRingHom (𝟙 (Spec R)) = (Scheme.ΓSpecIso R).inv.hom := by
  simp [structureRingHom]

end Flat

section Examples

abbrev tildeIntQuotient (I : Ideal ℤ) : (Spec (CommRingCat.of ℤ)).Modules :=
  tilde (R := CommRingCat.of ℤ) (ModuleCat.of ℤ (ℤ ⧸ I))

example (I : Ideal ℤ) : IsFiniteQC (tildeIntQuotient I) :=
  (isFiniteQC_tilde_iff _).2 (inferInstanceAs (Module.Finite ℤ (ℤ ⧸ I)))

example (I : Ideal ℤ) [hI : I.IsPrime] :
    assPoints (tildeIntQuotient I) = {(⟨I, hI⟩ : PrimeSpectrum ℤ)} := by
  have : IsNoetherianRing (CommRingCat.of ℤ) := inferInstanceAs (IsNoetherianRing ℤ)
  rw [assPoints_tilde]
  change PrimeSpectrum.asIdeal ⁻¹' associatedPrimes ℤ (ℤ ⧸ I) = {(⟨I, hI⟩ : PrimeSpectrum ℤ)}
  rw [associatedPrimes.eq_singleton_of_isPrimary hI.isPrimary, hI.radical]
  ext P
  simp [PrimeSpectrum.ext_iff]

example (I : Ideal ℤ) [hI : I.IsMaximal] : suppDim (tildeIntQuotient I) = 0 ∧
    suppDim (structureModule (Spec (CommRingCat.of ℤ))) = 1 := by
  constructor
  · have : Module.Finite (CommRingCat.of ℤ) (ModuleCat.of ℤ (ℤ ⧸ I)) :=
      inferInstanceAs (Module.Finite ℤ (ℤ ⧸ I))
    rw [suppDim_tilde]
    refine (Module.supportDim_quotient_eq_ringKrullDim I).trans ?_
    letI := Ideal.Quotient.field I
    exact ringKrullDim_eq_zero_of_field _
  · rw [suppDim_structureModule]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim ℤ).trans
      (IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField)

example : IsFlatOver (tilde (R := CommRingCat.of ℤ) (ModuleCat.of ℤ ℚ))
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom ∧
    ¬ IsFlatOver (tildeIntQuotient (Ideal.span {2})) (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom := by
  refine ⟨(isFlatOver_tilde_iff _).2 (IsLocalization.flat ℚ (nonZeroDivisors ℤ)), fun h ↦ ?_⟩
  have h : Module.Flat ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}) := (isFlatOver_tilde_iff _).1 h
  have h1 : (1 : ℤ ⧸ Ideal.span {(2 : ℤ)}) = 0 :=
    (Module.Flat.isSMulRegular_of_nonZeroDivisors (r := (2 : ℤ))
      (mem_nonZeroDivisors_of_ne_zero two_ne_zero)).right_eq_zero_of_smul (by
        rw [← Algebra.algebraMap_eq_smul_one]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
  have := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  omega

example (x : X) : Module.finrank (X.residueField x) (fibre (structureModule X) x) = 1 := by
  rw [(structureModuleFibreEquiv x).finrank_eq, Module.finrank_self]

end Examples

end GlobalTheory.QCoh
