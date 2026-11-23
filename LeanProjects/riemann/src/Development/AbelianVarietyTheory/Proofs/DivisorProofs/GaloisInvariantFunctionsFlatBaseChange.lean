import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.InvFun

open TensorProduct in

theorem alg_inv {R A R' B : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing B] [Algebra R A] [Algebra R R']
    [Algebra R B] [Algebra A B] [Algebra R' B] [IsScalarTower R A B] [IsScalarTower R R' B]
    [Algebra.IsPushout R A R' B] [Module.Flat R A] (hinj : Function.Injective (algebraMap R R'))
    {J : Type} [Finite J] (s : J → (R' →ₐ[R] R')) (hs : ∀ x : R', (∀ i, s i x = x) → x ∈ (algebraMap R R').range)
    (t : J → (B →+* B)) (htA : ∀ i a, t i (algebraMap A B a) = algebraMap A B a)
    (htR : ∀ i r, t i (algebraMap R' B r) = algebraMap R' B (s i r)) :
    Function.Injective (algebraMap A B) ∧ ∀ u : B, (∀ i, t i u = u) → u ∈ Set.range (algebraMap A B) := by
  classical
  cases nonempty_fintype J
  let e := Algebra.IsPushout.equiv R A R' B
  have he : ∀ (a : A) (r : R'), e (a ⊗ₜ r) = algebraMap A B a * algebraMap R' B r := fun a r =>
    Algebra.IsPushout.equiv_tmul R A R' B a r
  have hA : ∀ a : A, algebraMap A B a = e ((Algebra.linearMap R R').lTensor A (a ⊗ₜ 1)) := fun a => by
    simp [he]
  refine ⟨fun a b hab => ?_, fun u hu => ?_⟩
  · rw [hA, hA] at hab
    have h₁ := Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R R') hinj (e.injective hab)
    simpa using congrArg (TensorProduct.rid R A) h₁
  · let d : R' →ₗ[R] (J → R') := LinearMap.pi fun i => (s i).toLinearMap - LinearMap.id
    have hex : Function.Exact (Algebra.linearMap R R') d := by
      intro x
      constructor
      · intro hx
        exact hs x fun i => sub_eq_zero.1 (congrFun hx i)
      · rintro ⟨r, rfl⟩
        ext i
        simp [d]
    have hexA := Module.Flat.lTensor_exact A hex
    obtain ⟨w, rfl⟩ := e.surjective u
    have key : ∀ (w : A ⊗[R] R') (i : J), e (TensorProduct.piRight R R A (fun _ : J => R') (d.lTensor A w) i) =
        t i (e w) - e w := by
      intro w i
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; ring
      | tmul a r => simp [d, he, htA, htR, mul_sub, tmul_sub]
    have h0 : d.lTensor A w = 0 := by
      apply (TensorProduct.piRight R R A (fun _ : J => R')).injective
      ext i
      apply e.injective
      rw [key, hu]
      simp
    obtain ⟨v, rfl⟩ := (hexA w).1 h0
    refine ⟨TensorProduct.rid R A v, ?_⟩
    rw [hA]
    congr 2
    exact (TensorProduct.rid R A).symm_apply_apply v

theorem app_comp_appLE {Y Y' : Scheme.{0}} {β : Y' ⟶ Y} {f : Y' ⟶ Y'} (hf : f ≫ β = β) (U : Y.Opens)
    (e : β ⁻¹ᵁ U ≤ f ⁻¹ᵁ (β ⁻¹ᵁ U)) : β.app U ≫ f.appLE (β ⁻¹ᵁ U) (β ⁻¹ᵁ U) e = β.app U := by
  refine (Scheme.Hom.comp_appLE f β U (β ⁻¹ᵁ U) e).symm.trans ?_
  rw [← Scheme.Hom.appLE_eq_app]
  simp only [hf]

theorem const_comp_appLE {R : CommRingCat.{0}} {Y : Scheme.{0}} {y : Y ⟶ Spec R} {f : Y ⟶ Y} {s : R ⟶ R}
    (hf : f ≫ y = y ≫ Spec.map s) (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ U) :
    ((Scheme.ΓSpecIso R).inv ≫ y.appLE ⊤ U le_top) ≫ f.appLE U U e =
      s ≫ (Scheme.ΓSpecIso R).inv ≫ y.appLE ⊤ U le_top := by
  have e₁ : y.appLE ⊤ U le_top ≫ f.appLE U U e = (Spec.map s).appTop ≫ y.appLE ⊤ U le_top := by
    refine (Scheme.Hom.appLE_comp_appLE f y ⊤ U U le_top e).trans ?_
    simp only [hf]
    exact Scheme.Hom.comp_appLE y (Spec.map s) ⊤ U le_top
  rw [Category.assoc, e₁, Scheme.ΓSpecIso_inv_naturality_assoc]

theorem affine_inv {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (hG : IsGal ρ)
    {Y Y' : Scheme.{0}} {y : Y ⟶ Sp R} {y' : Y' ⟶ Sp R'} {β : Y' ⟶ Y} [Flat y] (h : IsPullback β y' y (spMap ρ))
    (act : Gal ρ → (Y' ⟶ Y')) (hβ : ∀ σ, act σ ≫ β = β) (hy : ∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ))
    {U : Y.Opens} (hU : IsAffineOpen U) :
    Function.Injective (β.app U).hom ∧ ∀ u : Γ(Y', β ⁻¹ᵁ U),
      (∀ σ (h : β ⁻¹ᵁ U ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ U)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (β.app U).hom := by
  have hp := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := β ⁻¹ᵁ U)
    le_top le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen h _ _ _
      (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have hp' : IsPushout ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top)
      (CommRingCat.ofHom ρ) (β.app U)
      ((Scheme.ΓSpecIso (.of R')).inv ≫ y'.appLE ⊤ (β ⁻¹ᵁ U) le_top) := by
    refine hp.of_iso (Scheme.ΓSpecIso _) (.refl _) (Scheme.ΓSpecIso _) (.refl _) (by simp) ?_
      (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    exact Scheme.ΓSpecIso_naturality _
  have hfl : ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
      (y.flat_appLE (isAffineOpen_top _) hU le_top)
  have hle : ∀ σ, β ⁻¹ᵁ U ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ U) := fun σ => by
    rw [← Scheme.Hom.comp_preimage, hβ]
  algebraize [ρ, ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top).hom,
    (β.app U).hom,
    ((Scheme.ΓSpecIso (.of R')).inv ≫ y'.appLE ⊤ (β ⁻¹ᵁ U) le_top).hom,
    (((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top) ≫ β.app U).hom]
  have : IsScalarTower R Γ(Y, U) Γ(Y', β ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower R R' Γ(Y', β ⁻¹ᵁ U) := .of_algebraMap_eq' congr($(hp'.w).hom)
  have : Algebra.IsPushout R Γ(Y, U) R' Γ(Y', β ⁻¹ᵁ U) :=
    CommRingCat.isPushout_iff_isPushout.mp hp'
  have := hG.1
  have H := alg_inv (R := R) (A := Γ(Y, U)) (R' := R') (B := Γ(Y', β ⁻¹ᵁ U)) hρ
    (fun σ : Gal ρ => (⟨Gal.hom σ, σ.2⟩ : R' →ₐ[R] R')) (fun x hx => hG.2 x fun σ hσ => hx ⟨σ, hσ⟩)
    (fun σ => ((act σ).appLE _ _ (hle σ)).hom) ?_ ?_
  · exact ⟨H.1, fun u hu => H.2 u fun σ => hu σ _⟩
  · intro σ a
    exact congr($(app_comp_appLE (hβ σ) U (hle σ)).hom a)
  · intro σ r
    exact congr($(const_comp_appLE (hy σ) (β ⁻¹ᵁ U) (hle σ)).hom r)

theorem app_res {Y Y' : Scheme.{0}} (β : Y' ⟶ Y) {U V : Y.Opens} (e : U ≤ V) (a : Γ(Y, V)) :
    (β.app U).hom ((Y.presheaf.map (homOfLE e).op).hom a) =
      (Y'.presheaf.map (homOfLE (β.preimage_mono e)).op).hom ((β.app V).hom a) :=
  congr($(β.naturality (homOfLE e).op).hom a)

theorem res_res {Y : Scheme.{0}} {U V W : Y.Opens} (e : U ≤ V) (e' : V ≤ W) (a : Γ(Y, W)) :
    (Y.presheaf.map (homOfLE e).op).hom ((Y.presheaf.map (homOfLE e').op).hom a) =
      (Y.presheaf.map (homOfLE (e.trans e')).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem le_iSup_affine {Y : Scheme.{0}} (V : Y.Opens) :
    V ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V}, U.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUV⟩, hxU⟩

theorem injective_of_affine {Y Y' : Scheme.{0}} (β : Y' ⟶ Y)
    (H : ∀ U : Y.Opens, IsAffineOpen U → Function.Injective (β.app U).hom) (V : Y.Opens) :
    Function.Injective (β.app V).hom := by
  intro a b hab
  refine Y.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => U.1) V
    (fun U => homOfLE U.2.2) (le_iSup_affine V) a b fun U => H U.1 U.2.1 ?_
  exact (app_res β U.2.2 a).trans ((congrArg _ hab).trans (app_res β U.2.2 b).symm)

theorem mem_range_of_affine {Y Y' : Scheme.{0}} (β : Y' ⟶ Y)
    (H : ∀ U : Y.Opens, Function.Injective (β.app U).hom) (V : Y.Opens) (u : Γ(Y', β ⁻¹ᵁ V))
    (hu : ∀ (U : Y.Opens) (_ : IsAffineOpen U) (e : U ≤ V),
      (Y'.presheaf.map (homOfLE (β.preimage_mono e)).op).hom u ∈ Set.range (β.app U).hom) :
    u ∈ Set.range (β.app V).hom := by
  choose a ha using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => hu U.1 U.2.1 U.2.2
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => U.1) V
    (fun U => homOfLE U.2.2) (le_iSup_affine V) a (fun i j => H (i.1 ⊓ j.1) (by
      refine (app_res β inf_le_left (a i)).trans (Eq.trans ?_ (app_res β inf_le_right (a j)).symm)
      rw [ha, ha, res_res, res_res]))
  refine ⟨s, Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => β ⁻¹ᵁ U.1) (β ⁻¹ᵁ V)
    (fun U => homOfLE (β.preimage_mono U.2.2)) ?_ _ _ fun U => ?_⟩
  · rw [← β.preimage_iSup]
    exact β.preimage_mono (le_iSup_affine V)
  · exact (app_res β U.2.2 s).symm.trans ((congrArg _ (hs U)).trans (ha U))

theorem invariant_functions : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R']
    (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y →
    IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) →
    (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ V : Y.Opens, Function.Injective (β.app V).hom ∧
    ∀ u : Γ(Y', β ⁻¹ᵁ V), (∀ σ (h : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) →
      u ∈ Set.range (β.app V).hom := by
  intro R _ _ R' _ _ _ ρ hF hG Y Y' y y' β _ h act hβ hy V
  have H := fun (U : Y.Opens) (hU : IsAffineOpen U) => affine_inv ρ hF.2.1 hG h act hβ hy hU
  have hinj := injective_of_affine β fun U hU => (H U hU).1
  refine ⟨hinj V, fun u hu => mem_range_of_affine β hinj V u fun U hU e => (H U hU).2 _ fun σ hσ => ?_⟩
  have hle : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, hβ]
  have e₁ : Y'.presheaf.map (homOfLE (β.preimage_mono e)).op ≫ (act σ).appLE _ _ hσ =
      (act σ).appLE _ _ hle ≫ Y'.presheaf.map (homOfLE (β.preimage_mono e)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  exact (congr($(e₁).hom u)).trans (congrArg _ (hu σ hle))

end GlobalTheory.Mum.InvFun
