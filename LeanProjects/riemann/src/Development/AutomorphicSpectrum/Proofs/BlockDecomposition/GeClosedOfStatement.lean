import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedImmersionPullbackKernelSup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSections

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening GlobalTheory.QCoh

namespace GlobalTheory.CompanionTheory.GE.Close

variable {X : Scheme.{0}}

abbrev fn (V : X.Opens) : Γ(𝟙_ X.Modules, V) ≃ₗ[Γ(X, V)] Γ(X, V) := structureModuleSectionsEquiv V

def subOf (J : X.IdealSheafData) : Subobject (𝟙_ X.Modules) := Subobject.mk (idealModuleι J)

theorem mem_secs_subOf (J : X.IdealSheafData) (V : X.affineOpens) (x : Γ(𝟙_ X.Modules, V.1)) :
    x ∈ secs (subOf J) V.1 ↔ fn V.1 x ∈ J.ideal V := by
  unfold secs subOf
  rw [← Subobject.underlyingIso_hom_comp_eq_mk, range_app_iso_comp,
    ← exists_idealModuleι_app_eq_iff_mem]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t, rfl⟩
  · rintro ⟨t, ht⟩; exact ⟨t, (fn V.1).injective ht⟩

theorem subOf_qcoh (J : X.IdealSheafData) : ((subOf J : Subobject _) : X.Modules).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (idealModuleι J)).symm inferInstance

theorem subOf_le_iff {J K : X.IdealSheafData} : subOf J ≤ subOf K ↔ J ≤ K := by
  rw [le_iff_secs_subset]
  constructor
  · intro h U a ha
    have := h U ((mem_secs_subOf J U ((fn U.1).symm a)).2 (by simpa using ha))
    simpa using (mem_secs_subOf K U _).1 this
  · intro h U x hx
    exact (mem_secs_subOf K U x).2 (h U ((mem_secs_subOf J U x).1 hx))

theorem subOf_sup (J K : X.IdealSheafData) : subOf (J ⊔ K) = subOf J ⊔ subOf K := by
  have hE : (𝟙_ X.Modules).IsQuasicoherent := (isCoherent_unit X).1
  obtain ⟨hq, hs⟩ := GlobalTheory.CompanionTheory.GE.supsecs hE (subOf J) (subOf K) (subOf_qcoh J) (subOf_qcoh K)
  apply le_antisymm
  · rw [le_iff_secs_subset]
    intro U x hx
    rw [hs U.1 U.2]
    have h1 := (mem_secs_subOf _ U x).1 hx
    rw [Scheme.IdealSheafData.ideal_sup] at h1
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    refine ⟨(fn U.1).symm a, (mem_secs_subOf J U _).2 (by simpa using ha),
      (fn U.1).symm b, (mem_secs_subOf K U _).2 (by simpa using hb), ?_⟩
    apply (fn U.1).injective
    simpa using hab.symm
  · exact sup_le (subOf_le_iff.2 le_sup_left) (subOf_le_iff.2 le_sup_right)

theorem eq_subOf_of_qcoh (B : Subobject (𝟙_ X.Modules)) (hB : (B : X.Modules).IsQuasicoherent) :
    ∃ J : X.IdealSheafData, subOf J = B := by
  have hE : (𝟙_ X.Modules).IsQuasicoherent := (isCoherent_unit X).1
  have : IsFiniteQC (𝟙_ X.Modules) := isFiniteQC_structureModule
  have hq : (cokernel B.arrow).IsQuasicoherent := inferInstance
  have : IsFiniteQC (cokernel B.arrow) := .of_epi (cokernel.π B.arrow)
  refine ⟨annihilatorSheaf (cokernel B.arrow), ?_⟩
  apply le_antisymm
  · rw [le_iff_secs_subset]
    intro U x hx
    have hA := (mem_secs_subOf _ U x).1 hx
    rw [annihilatorSheaf_ideal, Module.mem_annihilator] at hA
    have h0 := hA ((cokernel.π B.arrow).app U.1 ((fn U.1).symm 1))
    rw [← Scheme.Modules.Hom.app_smul] at h0
    have hx' : fn U.1 x • (fn U.1).symm 1 = x := by
      apply (fn U.1).injective
      simp
    rw [hx'] at h0
    exact (exact_cokernel_π_app B.arrow U.2 x).1 h0
  · rw [le_iff_secs_subset]
    rintro U x ⟨y, rfl⟩
    refine (mem_secs_subOf _ U _).2 ?_
    rw [annihilatorSheaf_ideal, Module.mem_annihilator]
    intro m
    obtain ⟨z, rfl⟩ := GroundTheory.Arith.SchemeCoh.surjective_cokernel_π_app B.arrow U.2 m
    rw [← Scheme.Modules.Hom.app_smul]
    have hc : fn U.1 (B.arrow.app U.1 y) • z = fn U.1 z • B.arrow.app U.1 y := by
      apply (fn U.1).injective
      simp [mul_comm]
    rw [hc, Scheme.Modules.Hom.app_smul, (exact_cokernel_π_app B.arrow U.2).apply_apply_eq_zero y,
      smul_zero]

theorem mono_cokernel_desc_of_exact {C : Type*} [Category C] [Abelian C] (S : ShortComplex C)
    (h : S.Exact) : Mono (cokernel.desc S.f S.g S.zero) :=
  S.exact_iff_mono_cokernel_desc.1 h

theorem supportedIn_cokernel_idealModuleι (J : X.IdealSheafData) :
    Scheme.Modules.SupportedIn (cokernel (idealModuleι J)) (J.support : Set X) := by
  have hpush : Scheme.Modules.SupportedIn
      ((Scheme.Modules.pushforward J.subschemeι).obj (structureModule J.subscheme))
      (J.support : Set X) := by
    refine ((Scheme.Modules.SupportedIn.univ _).pushforward J.subschemeι).mono ?_
    rintro _ ⟨z, -, rfl⟩
    exact J.range_subschemeι.le ⟨z, rfl⟩
  let S : ShortComplex X.Modules := ShortComplex.mk (idealModuleι J) (toSubscheme J) (kernel.condition _)
  have hex : S.Exact := ShortComplex.exact_kernel _
  have hm : Mono (cokernel.desc S.f S.g S.zero) := mono_cokernel_desc_of_exact S hex
  exact Scheme.Modules.SupportedIn.of_mono (cokernel.desc S.f S.g S.zero) hpush

theorem supportedIn_subOf (J : X.IdealSheafData) :
    Scheme.Modules.SupportedIn (cokernel (subOf J).arrow) (J.support : Set X) := by
  have e : (Subobject.underlyingIso (idealModuleι J)).hom ≫ idealModuleι J = (subOf J).arrow :=
    Subobject.underlyingIso_hom_comp_eq_mk _
  let i : cokernel (subOf J).arrow ≅ cokernel (idealModuleι J) :=
    cokernelIsoOfEq e.symm ≪≫ (cokernelEpiComp (Subobject.underlyingIso (idealModuleι J)).hom _)
  exact (supportedIn_cokernel_idealModuleι J).of_iso i.symm

theorem support_subset_of_supportedIn (J : X.IdealSheafData) {T : Set X} (hT : IsClosed T)
    (h : Scheme.Modules.SupportedIn (cokernel (subOf J).arrow) T) : (J.support : Set X) ⊆ T := by
  have hE : (𝟙_ X.Modules).IsQuasicoherent := (isCoherent_unit X).1
  have hq := subOf_qcoh J
  intro x hx
  by_contra hxT
  obtain ⟨U, ⟨V, hV, rfl⟩, hxV, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxT hT.isOpen_compl
  let W : X.affineOpens := ⟨V, hV⟩
  have h0 := h V (Set.disjoint_left.2 fun y hy hyT => hle hy hyT)
    ((cokernel.π (subOf J).arrow).app V ((fn V).symm 1))
  have h1 := (exact_cokernel_π_app (subOf J).arrow hV _).1 h0
  have h2 : (1 : Γ(X, V)) ∈ J.ideal W := by
    have := (mem_secs_subOf J W _).1 h1
    simpa [W] using this
  obtain ⟨t, ht⟩ := (exists_idealModuleι_app_eq_iff_mem J W 1).2 h2
  refine notMem_support_of_mem_basicOpen J t (x := x) ?_ hx
  rw [ht, Scheme.basicOpen_of_isUnit _ isUnit_one]
  exact hxV

theorem isProper_of_support_subset {S : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (J T : X.IdealSheafData)
    (hT : IsProper (T.subschemeι ≫ f)) (h : (J.support : Set X) ⊆ T.support) :
    IsProper (J.subschemeι ≫ f) := by
  let K : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal J.support
  have hJK : J ≤ K := (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal).1 le_rfl
  have hTK : T ≤ K := (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal).1 h
  have hKs : (K.support : Set X) = J.support := by
    simp [K]
  let p : K.subscheme ⟶ J.subscheme := IsClosedImmersion.lift J.subschemeι K.subschemeι
    (by simpa using hJK)
  let q : K.subscheme ⟶ T.subscheme := IsClosedImmersion.lift T.subschemeι K.subschemeι
    (by simpa using hTK)
  have hp : p ≫ J.subschemeι = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hq : q ≫ T.subschemeι = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hqc : IsClosedImmersion q := by
    have : IsClosedImmersion (q ≫ T.subschemeι) := by rw [hq]; infer_instance
    exact IsClosedImmersion.of_comp q T.subschemeι
  have hsurj : Surjective p := by
    refine ⟨fun z => ?_⟩
    have h1 : J.subschemeι z ∈ (K.support : Set X) := by
      rw [hKs]; exact J.range_subschemeι.le ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := K.range_subschemeι.ge h1
    refine ⟨w, J.subschemeι.isEmbedding.injective ?_⟩
    rw [← hw, ← hp]
    rfl
  have huc : UniversallyClosed (p ≫ J.subschemeι ≫ f) := by
    rw [← Category.assoc, hp, ← hq, Category.assoc]
    infer_instance
  have : UniversallyClosed (J.subschemeι ≫ f) := .of_comp_surjective p _
  exact ⟨⟩

section Core

variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [X.Over (Spec (.of R))]

theorem subOf_eq_powSub (Q : X.IdealSheafData) (n : ℕ)
    (hQ : ∀ U : X.affineOpens, Q.ideal U = Ideal.map (toFunctions (A := R) U.1) (I ^ n)) :
    subOf Q = powSub I (𝟙_ X.Modules) n := by
  have hE : (𝟙_ X.Modules).IsQuasicoherent := (isCoherent_unit X).1
  have key : ∀ (U : X.affineOpens) (x : Γ(𝟙_ X.Modules, U.1)),
      x ∈ secs (powSub I (𝟙_ X.Modules) n) U.1 ↔ fn U.1 x ∈ Q.ideal U := by
    intro U x
    rw [secs_powSub I _ hE n U.1 U.2, hQ U, SetLike.mem_coe]
    have e : Submodule.map (fn U.1).toLinearMap (Ideal.map (toFunctions (A := R) U.1) (I ^ n) • ⊤ :
        Submodule Γ(X, U.1) Γ(𝟙_ X.Modules, U.1)) = Ideal.map (toFunctions (A := R) U.1) (I ^ n) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
      simp
    constructor
    · intro h
      rw [← e]
      exact ⟨x, h, rfl⟩
    · intro h
      rw [← e] at h
      obtain ⟨y, hy, hyx⟩ := h
      have hxy : y = x := (fn U.1).injective hyx
      exact hxy ▸ hy
  apply le_antisymm
  · rw [le_iff_secs_subset]
    intro U x hx
    exact (key U x).2 ((mem_secs_subOf Q U x).1 hx)
  · rw [le_iff_secs_subset]
    intro U x hx
    exact (mem_secs_subOf Q U x).2 ((key U x).1 hx)

theorem exists_ideal_of_statement [IsSeparated (X ↘ Spec (.of R))]
    [LocallyOfFiniteType (X ↘ Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))]
    (hS : Statement I (⊥ : X.IdealSheafData)) (J Q : ℕ → X.IdealSheafData)
    (hQ : ∀ e, subOf (Q e) = powSub I (𝟙_ X.Modules) (e + 1)) (hJQ : ∀ e, Q e ≤ J e)
    (hsucc : ∀ e, J e = J (e + 1) ⊔ Q e)
    (hprop : IsProper ((J 0).subschemeι ≫ (X ↘ Spec (.of R)))) :
    ∃ JB : X.IdealSheafData, IsProper (JB.subschemeι ≫ (X ↘ Spec (.of R))) ∧
      ∀ e, JB ⊔ Q e = J e := by
  have hcs : ClosedSys I (𝟙_ X.Modules) (fun e => subOf (J e)) :=
    { qcoh := fun e => subOf_qcoh (J e)
      pow_le := fun e => by
        rw [← hQ]
        exact subOf_le_iff.2 (hJQ e)
      succ := fun e => by
        rw [← hQ, ← subOf_sup, ← hsucc] }
  have hk : ∀ e, Killed (⊥ : X.IdealSheafData) (subOf (J e)) := by
    intro e U a ha x
    have ha0 : a = 0 := by simpa using ha
    rw [ha0, zero_smul]
    exact ⟨0, map_zero _⟩
  obtain ⟨B, hBq, ⟨T, hT, hsup⟩, hB⟩ := hS (𝟙_ X.Modules) (isCoherent_unit X) _ hcs hk
    ⟨J 0, hprop, supportedIn_subOf (J 0)⟩
  obtain ⟨JB, rfl⟩ := eq_subOf_of_qcoh B hBq
  refine ⟨JB, isProper_of_support_subset _ JB T hT
    (support_subset_of_supportedIn JB T.support.isClosed hsup), fun e => ?_⟩
  have h1 : subOf (JB ⊔ Q e) = subOf (J e) := by
    rw [subOf_sup, hQ]
    exact hB e
  exact le_antisymm (subOf_le_iff.1 h1.le) (subOf_le_iff.1 h1.ge)

end Core

section Thick

variable {R : Type} [CommRing R] (I : Ideal R) [X.Over (Spec (.of R))]

theorem fromSpec_appTop {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec.appTop = X.presheaf.map (homOfLE le_top).op ≫ (Scheme.ΓSpecIso Γ(X, V)).inv := by
  have h := hV.fromSpec_app_of_le ⊤ le_top
  have e : ∀ i : (⊤ : (Spec Γ(X, V)).Opens) ⟶ ⊤, (Spec Γ(X, V)).presheaf.map i.op = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _)]
    simp
  refine h.trans ?_
  erw [e, Category.comp_id]
  rfl

theorem toFunctions_hom {V : X.Opens} :
    (Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop ≫ X.presheaf.map (homOfLE le_top).op =
      CommRingCat.ofHom (toFunctions (A := R) V) := by
  ext r
  rfl

theorem fromSpec_comp_over {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ (X ↘ Spec (.of R)) = Spec.map (CommRingCat.ofHom (toFunctions (A := R) V)) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, fromSpec_appTop,
    ← cancel_epi (Scheme.ΓSpecIso (.of R)).inv, ← Scheme.ΓSpecIso_inv_naturality,
    ← toFunctions_hom]
  simp only [Category.assoc]
  rfl

theorem toFunctions_mem_ker (e : ℕ) (U : X.affineOpens) (r : R) (hr : r ∈ I ^ (e + 1)) :
    (pullback.fst (X ↘ Spec (.of R)) (thick R I e)).app U.1 (toFunctions (A := R) U.1 r) = 0 := by
  set f := X ↘ Spec (.of R)
  set pr := pullback.fst f (thick R I e)
  have h1 : (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ pr.appTop =
      CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))) ≫
        (Scheme.ΓSpecIso (.of (R ⧸ I ^ (e + 1)))).inv ≫ (pullback.snd f (thick R I e)).appTop := by
    rw [← Scheme.Hom.comp_appTop, show pr ≫ f = _ from pullback.condition, Scheme.Hom.comp_appTop,
      ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have h2 : pr.appTop (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) = 0 := by
    have h4 := ConcreteCategory.congr_hom h1 r
    simp only [ConcreteCategory.comp_apply] at h4
    refine h4.trans ?_
    have h5 : (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) r = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 hr
    rw [h5, map_zero, map_zero]
  have nat := pr.naturality (homOfLE (le_top : U.1 ≤ ⊤)).op
  have h3 := ConcreteCategory.congr_hom nat (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))
  simp only [ConcreteCategory.comp_apply] at h3
  change pr.app U.1 (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
    (f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))) = 0
  refine h3.trans ?_
  erw [h2, map_zero]

theorem appLE_fromSpec {A : CommRingCat.{0}} {V : X.Opens} (hV : IsAffineOpen V)
    (q : CommRingCat.of Γ(X, V) ⟶ A) (h : ⊤ ≤ (Spec.map q ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (Spec.map q ≫ hV.fromSpec).appLE V ⊤ h = q ≫ (Scheme.ΓSpecIso A).inv := by
  rw [Scheme.Hom.comp_appLE, hV.fromSpec_app_self, Category.assoc]
  erw [Scheme.Hom.map_appLE]
  rw [Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem mem_of_app_eq_zero (e : ℕ) (U : X.affineOpens) (a : Γ(X, U.1))
    (ha : (pullback.fst (X ↘ Spec (.of R)) (thick R I e)).app U.1 a = 0) :
    a ∈ Ideal.map (toFunctions (A := R) U.1) (I ^ (e + 1)) := by
  have hU : IsAffineOpen U.1 := U.2
  set 𝔞 := Ideal.map (toFunctions (A := R) U.1) (I ^ (e + 1)) with h𝔞
  let v : R ⧸ I ^ (e + 1) →+* Γ(X, U.1) ⧸ 𝔞 :=
    Ideal.quotientMap 𝔞 (toFunctions (A := R) U.1) Ideal.le_comap_map
  let q : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of (Γ(X, U.1) ⧸ 𝔞) :=
    CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)
  let t : Spec (.of (Γ(X, U.1) ⧸ 𝔞)) ⟶ X := Spec.map q ≫ hU.fromSpec
  have hw : t ≫ (X ↘ Spec (.of R)) = Spec.map (CommRingCat.ofHom v) ≫ thick R I e := by
    simp only [t, Category.assoc, fromSpec_comp_over hU, ← Spec.map_comp]
    rfl
  let l := pullback.lift t (Spec.map (CommRingCat.ofHom v)) hw
  have hl : l ≫ pullback.fst (X ↘ Spec (.of R)) (thick R I e) = t := pullback.lift_fst _ _ _
  have hh : ⊤ ≤ t ⁻¹ᵁ U.1 := by
    intro z _
    change (Spec.map q ≫ hU.fromSpec) z ∈ U.1
    rw [Scheme.Hom.comp_apply]
    exact hU.range_fromSpec.le ⟨_, rfl⟩
  have e1 : ∀ (g : Spec (.of (Γ(X, U.1) ⧸ 𝔞)) ⟶ X) (hg : l ≫ pullback.fst (X ↘ Spec (.of R)) (thick R I e) = g)
      (h : ⊤ ≤ g ⁻¹ᵁ U.1), g.appLE U.1 ⊤ h a = 0 := by
    rintro _ rfl h
    rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ha, map_zero]
  have e2 := e1 t hl hh
  rw [show t.appLE U.1 ⊤ hh = _ from appLE_fromSpec hU q hh, CommRingCat.comp_apply] at e2
  have e3 : q a = 0 := by
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback (Scheme.ΓSpecIso _).inv)
    rw [e2, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.1 e3

theorem ideal_ker_thick (e : ℕ) (U : X.affineOpens) :
    (pullback.fst (X ↘ Spec (.of R)) (thick R I e)).ker.ideal U =
      Ideal.map (toFunctions (A := R) U.1) (I ^ (e + 1)) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [Scheme.Hom.ker_apply]
  apply le_antisymm
  · intro a ha
    exact mem_of_app_eq_zero I e U a ha
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    exact toFunctions_mem_ker I e U r hr

end Thick

section Main

theorem isClosedImmersion_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    IsClosedImmersion (thick R I e) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem thickMap_fst {R : Type} [CommRing R] (I : Ideal R) (e : ℕ)
    (P : Over (Spec (CommRingCat.of R))) :
    thickMap R I e P ≫ pullback.fst P.hom (thick R I (e + 1)) = pullback.fst P.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem geClosed_of_statement :
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
      ∀ (X : Scheme.{0}) [X.Over (Spec (.of R))] [IsSeparated (X ↘ Spec (.of R))]
        [LocallyOfFiniteType (X ↘ Spec (.of R))] [QuasiCompact (X ↘ Spec (.of R))],
        Statement I (⊥ : X.IdealSheafData)) → GEClosed := by
  intro H R _ _ I hI P hsep hlft hqc C i β hi hβ hprop
  letI : P.left.Over (Spec (.of R)) := ⟨P.hom⟩
  have hf : (P.left ↘ Spec (.of R)) = P.hom := rfl
  haveI : IsSeparated (P.left ↘ Spec (.of R)) := hsep
  haveI : LocallyOfFiniteType (P.left ↘ Spec (.of R)) := hlft
  haveI : QuasiCompact (P.left ↘ Spec (.of R)) := hqc
  have hthick : ∀ e, IsClosedImmersion (thick R I e) := isClosedImmersion_thick I
  let pr : ∀ e, (thickObj R I e P).left ⟶ P.left := fun e => pullback.fst P.hom (thick R I e)
  haveI hpr : ∀ e, IsClosedImmersion (pr e) := fun e => by
    have := hthick e
    change IsClosedImmersion (pullback.fst P.hom (thick R I e))
    infer_instance
  have hmapfst : ∀ e, thickMap R I e P ≫ pr (e + 1) = pr e := fun e => thickMap_fst I e P
  haveI hmap : ∀ e, IsClosedImmersion (thickMap R I e P) := fun e => by
    have : IsClosedImmersion (thickMap R I e P ≫ pr (e + 1)) := by
      rw [hmapfst]; exact hpr e
    exact IsClosedImmersion.of_comp_isClosedImmersion _ (pr (e + 1))
  haveI := hi
  let c : ∀ e, C e ⟶ P.left := fun e => i e ≫ pr e
  haveI hc : ∀ e, IsClosedImmersion (c e) := fun e => inferInstance
  let J : ℕ → P.left.IdealSheafData := fun e => (c e).ker
  let Q : ℕ → P.left.IdealSheafData := fun e => (pr e).ker
  have hQ : ∀ e, subOf (Q e) = powSub I (𝟙_ P.left.Modules) (e + 1) := fun e =>
    subOf_eq_powSub I (Q e) (e + 1) (fun U => ideal_ker_thick I e U)
  have hJQ : ∀ e, Q e ≤ J e := fun e => Scheme.Hom.le_ker_comp _ _
  have hsucc : ∀ e, J e = J (e + 1) ⊔ Q e := by
    intro e
    have h := ker_inter_eq_sup (pr (e + 1)) (i (e + 1)) (thickMap R I e P) (β e) (i e) (hβ e)
    rw [hmapfst] at h
    have h2 : (β e ≫ i (e + 1)) ≫ pr (e + 1) = c e := by
      rw [(hβ e).w, Category.assoc, hmapfst]
    rw [h2] at h
    exact h
  have hprop0 : IsProper ((J 0).subschemeι ≫ (P.left ↘ Spec (.of R))) := by
    let u : (J 0).subscheme ⟶ C 0 := IsClosedImmersion.lift (c 0) (J 0).subschemeι
      (by simp [J])
    let w : C 0 ⟶ (J 0).subscheme := IsClosedImmersion.lift (J 0).subschemeι (c 0)
      (by simp [J])
    have hu : u ≫ c 0 = (J 0).subschemeι := IsClosedImmersion.lift_fac _ _ _
    have hw : w ≫ (J 0).subschemeι = c 0 := IsClosedImmersion.lift_fac _ _ _
    haveI : IsIso u := ⟨w, by rw [← cancel_mono (J 0).subschemeι, Category.assoc, hw, hu, Category.id_comp],
      by rw [← cancel_mono (c 0), Category.assoc, hu, hw, Category.id_comp]⟩
    have hthick0 := hthick 0
    have hc0 : c 0 ≫ P.hom = (i 0 ≫ (thickObj R I 0 P).hom) ≫ thick R I 0 := by
      simp only [c, pr, Category.assoc]
      rw [pullback.condition]
      rfl
    rw [hf, ← hu, Category.assoc, hc0]
    infer_instance
  obtain ⟨JB, hJB, hsup⟩ := exists_ideal_of_statement I (H R I hI P.left) J Q hQ hJQ hsucc hprop0
  let j := JB.subschemeι
  have hker : ∀ e, j.ker ≤ (c e).ker := fun e => by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    change JB ≤ J e
    rw [← hsup e]
    exact le_sup_left
  let b : ∀ e, C e ⟶ JB.subscheme := fun e => IsClosedImmersion.lift j (c e) (hker e)
  have hb : ∀ e, b e ≫ j = c e := fun e => IsClosedImmersion.lift_fac _ _ _
  refine ⟨JB.subscheme, j, b, inferInstance, hJB, fun e => ?_, fun e => ?_⟩
  · haveI : IsClosedImmersion (b e ≫ j) := by rw [hb]; exact hc e
    refine GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup j (pr e) (b e) (i e) (hb e) ?_
    rw [hb, Scheme.IdealSheafData.ker_subschemeι]
    exact (hsup e).symm
  · rw [← cancel_mono j, Category.assoc, hb, hb]
    change β e ≫ i (e + 1) ≫ pr (e + 1) = i e ≫ pr e
    rw [← Category.assoc, (hβ e).w, Category.assoc, hmapfst]

end Main

end GlobalTheory.CompanionTheory.GE.Close
