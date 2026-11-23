import Mathlib

open TensorProduct

namespace GlobalTheory

namespace Descent

section Algebra

variable {A : Type*} (A' : Type*) [CommRing A] [CommRing A'] [Algebra A A']
  [Module.FaithfullyFlat A A'] {M : Type*} [AddCommGroup M] [Module A M]

theorem finite [Module.Finite A' (A' ⊗[A] M)] : Module.Finite A M :=
  Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A'

theorem flat [Module.Flat A' (A' ⊗[A] M)] : Module.Flat A M :=
  Module.Flat.of_flat_tensorProduct A M A'

theorem fg_of_baseChange {N : Submodule A M} (h : (N.baseChange A').FG) : N.FG := by
  have hinj : Function.Injective (N.subtype.baseChange A') :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := A') N.subtype N.injective_subtype
  have e : A' ⊗[A] N ≃ₗ[A'] N.baseChange A' := LinearEquiv.ofInjective _ hinj
  have : Module.Finite A' (N.baseChange A') := Module.Finite.iff_fg.mpr h
  have : Module.Finite A' (A' ⊗[A] N) := Module.Finite.equiv e.symm
  exact Module.Finite.iff_fg.mp (finite A')

theorem finitePresentation [Module.FinitePresentation A' (A' ⊗[A] M)] :
    Module.FinitePresentation A M := by
  have : Module.Finite A M := finite A'
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  refine Module.finitePresentation_of_free_of_surjective f hf (fg_of_baseChange A' ?_)
  have hf' : Function.Surjective (f.baseChange A') := LinearMap.lTensor_surjective A' hf
  have hker : (LinearMap.ker f).baseChange A' = LinearMap.ker (f.baseChange A') := by
    have hex : Function.Exact ((LinearMap.ker f).subtype.baseChange A') (f.baseChange A') :=
      lTensor_exact A' (LinearMap.exact_subtype_ker_map f) hf
    exact (LinearMap.exact_iff.mp hex).symm
  rw [hker]
  exact Module.FinitePresentation.fg_ker _ hf'

theorem projective [Module.Finite A' (A' ⊗[A] M)] [Module.Projective A' (A' ⊗[A] M)] :
    Module.Projective A M := by
  have : Module.FinitePresentation A' (A' ⊗[A] M) := Module.finitePresentation_of_projective _ _
  have : Module.FinitePresentation A M := finitePresentation A'
  have : Module.Flat A M := flat A'
  exact Module.Flat.projective_of_finitePresentation

theorem rankAtStalk_eq [Module.Finite A' (A' ⊗[A] M)] [Module.Flat A' (A' ⊗[A] M)] {r : ℕ}
    (h : ∀ q : PrimeSpectrum A', Module.rankAtStalk (A' ⊗[A] M) q = r) (p : PrimeSpectrum A) :
    Module.rankAtStalk M p = r := by
  have : Module.Finite A M := finite A'
  have : Module.Flat A M := flat A'
  obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := A') p
  rw [← Module.rankAtStalk_baseChange, h]

theorem one_tmul_injective : Function.Injective fun m : M ↦ (1 : A') ⊗ₜ[A] m :=
  Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := A') M

theorem linearIndependent_iff {ι : Type*} (v : ι → M) :
    LinearIndependent A v ↔ LinearIndependent A' fun i ↦ (1 : A') ⊗ₜ[A] v i := by
  refine ⟨fun h ↦ Module.Flat.linearIndependent_one_tmul h, fun h ↦ ?_⟩
  have h' : LinearIndependent A fun i ↦ (1 : A') ⊗ₜ[A] v i :=
    h.restrict_scalars' A
  exact LinearIndependent.of_comp (TensorProduct.mk A A' M 1) h'

theorem algebraMap_dvd_iff (a b : A) : algebraMap A A' a ∣ algebraMap A A' b ↔ a ∣ b := by
  rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton,
    ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := A') (Ideal.span {a}), Ideal.mem_comap,
    Ideal.map_span, Set.image_singleton]

end Algebra

section IsBaseChange

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [Module.FaithfullyFlat A A']
  {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module A' M']
  [IsScalarTower A A' M'] {f : M →ₗ[A] M'} (hf : IsBaseChange A' f)

include hf

theorem finite_of_isBaseChange [Module.Finite A' M'] : Module.Finite A M :=
  have := Module.Finite.equiv hf.equiv.symm
  finite A'

theorem projective_of_isBaseChange [Module.Finite A' M'] [Module.Projective A' M'] :
    Module.Projective A M :=
  have := Module.Finite.equiv hf.equiv.symm
  have := Module.Projective.of_equiv hf.equiv.symm
  projective A'

end IsBaseChange

section Scheme

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}} (F : X.Modules)

noncomputable instance stalkModule (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x

theorem germ_smul (U : X.Opens) (x : X) (hx : x ∈ U) (r : Γ(X, U)) (m : Γ(F, U)) :
    F.presheaf.germ U x hx (r • m) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx m :=
  PresheafOfModules.germ_smul (R := X.presheaf) F.val x U hx r m

variable {F} {U : X.Opens} {s : Γ(F, U)}

theorem injective_smul_of_stalk {V : X.Opens} (hV : V ≤ U)
    (h : ∀ (x : X) (hx : x ∈ V), Function.Injective
      fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x (hV hx) s) :
    Function.Injective fun a : Γ(X, V) ↦ a • F.presheaf.map (homOfLE hV).op s := by
  intro a b hab
  apply TopCat.Presheaf.section_ext X.sheaf V a b
  intro x hx
  apply h x hx
  have := congrArg (F.presheaf.germ V x hx) hab
  simp only [germ_smul, TopCat.Presheaf.germ_res_apply] at this
  exact this

theorem bijective_smul_of_stalk
    (h : ∀ (x : X) (hx : x ∈ U), Function.Bijective
      fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x hx s)
    {V : X.Opens} (hV : V ≤ U) :
    Function.Bijective fun a : Γ(X, V) ↦ a • F.presheaf.map (homOfLE hV).op s := by
  refine ⟨injective_smul_of_stalk hV fun x hx ↦ (h x (hV hx)).1, fun t ↦ ?_⟩
  have hloc : ∀ x : V, ∃ (W : X.Opens) (_ : x.1 ∈ W) (hW : W ≤ V) (a : Γ(X, W)),
      a • F.presheaf.map (homOfLE (hW.trans hV)).op s = F.presheaf.map (homOfLE hW).op t := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha⟩ := (h x (hV hx)).2 (F.presheaf.germ V x hx t)
    obtain ⟨W, hWV, hxW, a, rfl⟩ := X.presheaf.exists_le_germ_eq a hx
    have h₁ : F.presheaf.germ W x hxW (a • F.presheaf.map (homOfLE (hWV.trans hV)).op s) =
        F.presheaf.germ V x hx t := by
      rw [germ_smul, TopCat.Presheaf.germ_res_apply]
      exact ha
    obtain ⟨W', hxW', i₁, i₂, e⟩ := F.presheaf.germ_eq x hxW hx _ _ h₁
    refine ⟨W', hxW', i₂.le, X.presheaf.map i₁.op a, ?_⟩
    rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp] at e
    exact e
  choose W hxW hWV a ha using hloc
  have hcover : V ≤ iSup W := fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf W a := by
    intro i j
    have hij : W i ⊓ W j ≤ U := inf_le_left.trans ((hWV i).trans hV)
    apply injective_smul_of_stalk (s := s) hij fun x hx ↦ (h x (hij hx)).1
    have e₁ := congrArg (F.presheaf.map (Opens.infLELeft (W i) (W j)).op) (ha i)
    have e₂ := congrArg (F.presheaf.map (Opens.infLERight (W i) (W j)).op) (ha j)
    rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp,
      ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp] at e₁ e₂
    exact e₁.trans e₂.symm
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i ↦ homOfLE (hWV i)) hcover a hcomp
  refine ⟨b, ?_⟩
  change Γ(X, V) at b
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) W V
    (fun i ↦ homOfLE (hWV i)) hcover
  intro i
  have hb' : X.presheaf.map (homOfLE (hWV i)).op b = a i := hb i
  change F.presheaf.map (homOfLE (hWV i)).op (b • F.presheaf.map (homOfLE hV).op s) =
    F.presheaf.map (homOfLE (hWV i)).op t
  rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp, hb', ← ha i]
  rfl

theorem bijective_smul_stalk
    (h : ∀ (V : X.Opens) (hV : V ≤ U),
      Function.Bijective fun a : Γ(X, V) ↦ a • F.presheaf.map (homOfLE hV).op s)
    (x : X) (hx : x ∈ U) :
    Function.Bijective fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x hx s := by
  constructor
  · intro a b hab
    obtain ⟨V, hVU, hxV, a, rfl⟩ := X.presheaf.exists_le_germ_eq a hx
    obtain ⟨W, hWV, hxW, b, rfl⟩ := X.presheaf.exists_le_germ_eq b hxV
    have h₁ : F.presheaf.germ V x hxV (a • F.presheaf.map (homOfLE hVU).op s) =
        F.presheaf.germ W x hxW (b • F.presheaf.map (homOfLE (hWV.trans hVU)).op s) := by
      rw [germ_smul, germ_smul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
      exact hab
    obtain ⟨W', hxW', i₁, i₂, e⟩ := F.presheaf.germ_eq x hxV hxW _ _ h₁
    rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp,
      Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp] at e
    exact X.presheaf.germ_ext W' hxW' i₁ i₂ ((h W' (i₁.le.trans hVU)).1 e)
  · intro t
    obtain ⟨V, hVU, hxV, t, rfl⟩ := F.presheaf.exists_le_germ_eq t hx
    obtain ⟨a, rfl⟩ := (h V hVU).2 t
    refine ⟨X.presheaf.germ V x hxV a, ?_⟩
    simp only [germ_smul, TopCat.Presheaf.germ_res_apply]

variable (s) in

noncomputable def sectionHom :
    @Quiver.Hom (U : Scheme.{u}).Modules _ (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)
      (F.restrict U.ι) :=
  (SheafOfModules.unitHomEquiv (F.restrict U.ι)).symm
    (PresheafOfModules.sectionsMk
      (fun W ↦ F.presheaf.map (homOfLE (U.ι_image_le W.unop)).op s)
      (fun W W' i ↦ by
        change F.presheaf.map _ (F.presheaf.map _ s) = _
        rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
        rfl))

variable (s) in

theorem sectionHom_app (W : (U : Scheme.{u}).Opens) (a : Γ(X, U.ι ''ᵁ W)) :
    ((sectionHom s).app W a : Γ(F, U.ι ''ᵁ W)) =
      a • F.presheaf.map (homOfLE (U.ι_image_le W)).op s := by
  have h1 : (sectionHom s).app W (1 : Γ((U : Scheme.{u}), W)) =
      F.presheaf.map (homOfLE (U.ι_image_le W)).op s := by
    have := SheafOfModules.unitHomEquiv_apply_coe (F.restrict U.ι) (sectionHom s) (op W)
    rw [sectionHom, Equiv.apply_symm_apply] at this
    exact this.symm
  have h2 := Scheme.Modules.Hom.app_smul (sectionHom s) (U := W) a (1 : Γ((U : Scheme.{u}), W))
  have h3 : a = a * 1 := (mul_one a).symm
  refine (congrArg ((sectionHom s).app W) h3).trans (h2.trans ?_)
  rw [h1]
  change ((U.ι.appIso W).inv a) • F.presheaf.map (homOfLE (U.ι_image_le W)).op s = _
  rw [Scheme.Opens.ι_appIso]
  rfl

theorem isIso_sectionHom_iff :
    IsIso (sectionHom s) ↔ ∀ (x : X) (hx : x ∈ U), Function.Bijective
      fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x hx s := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.trans ?_
  have key (W : (U : Scheme.{u}).Opens) : IsIso ((sectionHom s).app W) ↔ Function.Bijective
      fun a : Γ(X, U.ι ''ᵁ W) ↦ a • F.presheaf.map (homOfLE (U.ι_image_le W)).op s := by
    rw [ConcreteCategory.isIso_iff_bijective, ← funext (sectionHom_app s W)]
    rfl
  simp_rw [key]
  refine ⟨fun h ↦ bijective_smul_stalk fun V hV ↦ ?_, fun h W ↦ bijective_smul_of_stalk h _⟩
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hV]
  obtain ⟨W, rfl⟩ : ∃ W, U.ι ''ᵁ W = V := ⟨_, e⟩
  exact h W

noncomputable def freeIso
    (h : ∀ (x : X) (hx : x ∈ U), Function.Bijective
      fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x hx s) :
    @Iso (U : Scheme.{u}).Modules _ (SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)
      (F.restrict U.ι) :=
  @asIso _ _ _ _ (sectionHom s) (isIso_sectionHom_iff.mpr h)

@[simp]
theorem freeIso_hom
    (h : ∀ (x : X) (hx : x ∈ U), Function.Bijective
      fun a : X.presheaf.stalk x ↦ a • F.presheaf.germ U x hx s) :
    (freeIso h).hom = sectionHom s := rfl

end Scheme

end Descent

end GlobalTheory
