import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAppTopEqOfEffectiveEpi

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace GlobalFunctions

def FibreInjective : Prop :=
  ∀ (R₀ R C₀ C₁ : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R] [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁] [Module.Flat R₀ C₀] [Module.Flat R₀ C₁] (φ : C₀ →ₗ[R₀] C₁), (∀ (k : Type) [Field k] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k], Function.Injective (φ.baseChange k)) → Function.Injective (φ.baseChange R)

def SmoothDescent : Prop :=
  ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] (f g : B →ₐ[R] C) (r : B →ₐ[R] R), ∃ (R₀ B₀ C₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (_ : Algebra R₀ R) (_ : CommRing B₀) (_ : CommRing C₀) (_ : Algebra R₀ B₀) (_ : Algebra R₀ C₀) (f₀ g₀ : B₀ →ₐ[R₀] C₀) (r₀ : B₀ →ₐ[R₀] R₀) (β' : TensorProduct R₀ R B₀ ≃ₐ[R] B) (δ' : TensorProduct R₀ R C₀ ≃ₐ[R] C), Module.Flat R₀ B₀ ∧ Module.Flat R₀ C₀ ∧ ∀ b : B₀, f (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ f₀ b) ∧ g (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ g₀ b) ∧ r (β' (1 ⊗ₜ b)) = algebraMap R₀ R (r₀ b)

section Algebra

theorem baseChange_model {R₀ R k B₀ B C₀ C : Type} [CommRing R₀] [CommRing R] [CommRing k]
    [Algebra R₀ R] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k]
    [AddCommGroup B₀] [Module R₀ B₀] [AddCommGroup C₀] [Module R₀ C₀]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (β : R ⊗[R₀] B₀ ≃ₗ[R] B) (δ : R ⊗[R₀] C₀ ≃ₗ[R] C) (u₀ : B₀ →ₗ[R₀] C₀) (u : B →ₗ[R] C)
    (h : ∀ b, u (β (1 ⊗ₜ b)) = δ (1 ⊗ₜ u₀ b)) (y : k ⊗[R₀] B₀) :
    u.baseChange k (β.toLinearMap.baseChange k
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k B₀).symm y)) =
    δ.toLinearMap.baseChange k
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k C₀).symm (u₀.baseChange k y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c b => simp [h]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem model_apply {R₀ R B₀ B C₀ C : Type} [CommRing R₀] [CommRing R]
    [Algebra R₀ R] [AddCommGroup B₀] [Module R₀ B₀] [AddCommGroup C₀] [Module R₀ C₀]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (β : R ⊗[R₀] B₀ ≃ₗ[R] B) (δ : R ⊗[R₀] C₀ ≃ₗ[R] C) (u₀ : B₀ →ₗ[R₀] C₀) (u : B →ₗ[R] C)
    (h : ∀ b, u (β (1 ⊗ₜ b)) = δ (1 ⊗ₜ u₀ b)) (y : R ⊗[R₀] B₀) :
    u (β y) = δ (u₀.baseChange R y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have h1 : ∀ {M : Type} [AddCommGroup M] [Module R₀ M] (m : M),
        (c ⊗ₜ[R₀] m : R ⊗[R₀] M) = c • (1 ⊗ₜ m) := by
      intro M _ _ m
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [LinearMap.baseChange_tmul, h1 b, h1 (u₀ b), map_smul, map_smul, map_smul, h]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem eq_zero_of_fibres (hI : FibreInjective) (hD : SmoothDescent) {R B C : Type} [CommRing R]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C]
    (f g : B →ₐ[R] C) (r : B →ₐ[R] R)
    (hk : ∀ (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] B),
      f.toLinearMap.baseChange k x = g.toLinearMap.baseChange k x →
      r.toLinearMap.baseChange k x = 0 → x = 0)
    (b : B) (hb : f b = g b) (hr : r b = 0) : b = 0 := by
  obtain ⟨R₀, B₀, C₀, _, _, _, _, _, _, _, f₀, g₀, r₀, β, δ, _, _, h⟩ := hD R B C f g r
  let ρ : R ⊗[R₀] R₀ ≃ₗ[R] R := AlgebraTensorModule.rid R₀ R R
  have hf : ∀ b, f.toLinearMap (β.toLinearEquiv (1 ⊗ₜ b)) =
      δ.toLinearEquiv (1 ⊗ₜ f₀.toLinearMap b) := fun b ↦ (h b).1
  have hg : ∀ b, g.toLinearMap (β.toLinearEquiv (1 ⊗ₜ b)) =
      δ.toLinearEquiv (1 ⊗ₜ g₀.toLinearMap b) := fun b ↦ (h b).2.1
  have hr' : ∀ b, r.toLinearMap (β.toLinearEquiv (1 ⊗ₜ b)) =
      ρ (1 ⊗ₜ r₀.toLinearMap b) := fun b ↦ (h b).2.2.trans (by
        simp [ρ, Algebra.algebraMap_eq_smul_one])
  let φ : B₀ →ₗ[R₀] C₀ × R₀ := (f₀.toLinearMap - g₀.toLinearMap).prod r₀.toLinearMap
  have : Module.Flat R₀ (C₀ × R₀) := flat_prod
  have hφ : Function.Injective (φ.baseChange R) := by
    refine hI R₀ R B₀ (C₀ × R₀) φ fun k _ _ _ _ ↦ ?_
    rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : (f₀.toLinearMap - g₀.toLinearMap).baseChange k y = 0 := by
      have : f₀.toLinearMap - g₀.toLinearMap = (LinearMap.fst R₀ C₀ R₀) ∘ₗ φ := rfl
      rw [this, LinearMap.baseChange_comp, LinearMap.comp_apply, hy, map_zero]
    have h2 : r₀.toLinearMap.baseChange k y = 0 := by
      have : r₀.toLinearMap = (LinearMap.snd R₀ C₀ R₀) ∘ₗ φ := rfl
      rw [this, LinearMap.baseChange_comp, LinearMap.comp_apply, hy, map_zero]
    rw [LinearMap.baseChange_sub, LinearMap.sub_apply, sub_eq_zero] at h1
    have h3 := hk k (β.toLinearEquiv.toLinearMap.baseChange k
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k B₀).symm y))
      (by rw [baseChange_model _ _ _ _ hf, baseChange_model _ _ _ _ hg, h1])
      (by rw [baseChange_model _ _ _ _ hr', h2, map_zero, map_zero])
    have h4 : (β.toLinearEquiv.baseChange R k _ _)
      ((AlgebraTensorModule.cancelBaseChange R₀ R k k B₀).symm y) = 0 := h3
    simpa using h4
  obtain ⟨y, rfl⟩ := β.surjective b
  have h1 : f₀.toLinearMap.baseChange R y = g₀.toLinearMap.baseChange R y := by
    apply δ.toLinearEquiv.injective
    rw [← model_apply _ _ _ _ hf, ← model_apply _ _ _ _ hg]
    exact hb
  have h2 : r₀.toLinearMap.baseChange R y = 0 := by
    apply ρ.injective
    rw [← model_apply _ _ _ _ hr', map_zero]
    exact hr
  have h3 : φ = LinearMap.inl R₀ C₀ R₀ ∘ₗ (f₀.toLinearMap - g₀.toLinearMap) +
      LinearMap.inr R₀ C₀ R₀ ∘ₗ r₀.toLinearMap := by
    ext x <;> simp [φ]
  have : y = 0 := by
    apply hφ
    rw [map_zero, h3, LinearMap.baseChange_add, LinearMap.add_apply, LinearMap.baseChange_comp,
      LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply, h2,
      LinearMap.baseChange_sub, LinearMap.sub_apply, h1, sub_self, map_zero, map_zero, add_zero]
  rw [this, map_zero]

end Algebra

section Geometry

variable {R B C : CommRingCat.{0}} {X : Scheme.{0}}

theorem exists_eq_of_eq (i : Spec B ⟶ X) [EffectiveEpi i] {f g : B ⟶ C}
    (H : IsPullback (Spec.map f) (Spec.map g) i i) (x : B) (hx : f x = g x) :
    ∃ a : Γ(X, ⊤), (i.appTop ≫ (Scheme.ΓSpecIso B).hom) a = x := by
  obtain ⟨a, ha⟩ := FlatDescent.exists_appTop_eq_of_effectiveEpi i H
    ((Scheme.ΓSpecIso B).inv x) (by
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, CommRingCat.comp_apply, hx])
  exact ⟨a, by rw [CommRingCat.comp_apply, ha, Iso.inv_hom_id_apply]⟩

theorem appTop_comp_eq {p : X ⟶ Spec R} {i : Spec B ⟶ X} {φ : R ⟶ B}
    (hφ : i ≫ p = Spec.map φ) :
    p.appTop ≫ i.appTop ≫ (Scheme.ΓSpecIso B).hom = (Scheme.ΓSpecIso R).hom ≫ φ := by
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hφ, Scheme.ΓSpecIso_naturality]

theorem eq_zero_of_surjective {p : X ⟶ Spec R} (hp : Function.Surjective p.appTop)
    (i : Spec B ⟶ X) [EffectiveEpi i] {f g : B ⟶ C}
    (H : IsPullback (Spec.map f) (Spec.map g) i i) {φ : R ⟶ B} (hφ : i ≫ p = Spec.map φ)
    {R' : CommRingCat.{0}} (r : B ⟶ R') (hr : Function.Injective (φ ≫ r)) (x : B)
    (hx : f x = g x) (hrx : r x = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := exists_eq_of_eq i H x hx
  obtain ⟨c, rfl⟩ := hp a
  rw [← CommRingCat.comp_apply p.appTop, appTop_comp_eq hφ, CommRingCat.comp_apply] at hrx ⊢
  have : (Scheme.ΓSpecIso R).hom c = 0 := hr (hrx.trans (map_zero _).symm)
  rw [this, map_zero]

end Geometry

section Core

variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  {X : Scheme.{0}}

noncomputable abbrev prR (R k B : Type) [CommRing R] [CommRing k] [CommRing B] [Algebra R k]
    [Algebra R B] : Spec (.of (k ⊗[R] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := B)).toRingHom)

noncomputable abbrev prL (R k B : Type) [CommRing R] [CommRing k] [CommRing B] [Algebra R k]
    [Algebra R B] : Spec (.of (k ⊗[R] B)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (k ⊗[R] B)))

theorem isPullback_pr (R k B : Type) [CommRing R] [CommRing k] [CommRing B] [Algebra R k]
    [Algebra R B] : IsPullback (prR R k B) (prL R k B)
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R k))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R k B)).flip

noncomputable abbrev bc (k : Type) [CommRing k] [Algebra R k] (f : B →ₐ[R] C) :
    CommRingCat.of (k ⊗[R] B) ⟶ CommRingCat.of (k ⊗[R] C) :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id k k) f).toRingHom

theorem bc_apply (k : Type) [CommRing k] [Algebra R k] (f : B →ₐ[R] C) (x : k ⊗[R] B) :
    bc k f x = f.toLinearMap.baseChange k x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem bc_prR (k : Type) [CommRing k] [Algebra R k] (f : B →ₐ[R] C) :
    Spec.map (bc k f) ≫ prR R k B = prR R k C ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem bc_prL (k : Type) [CommRing k] [Algebra R k] (f : B →ₐ[R] C) :
    Spec.map (bc k f) ≫ prL R k B = prL R k C := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

theorem specMap_algHom (f : B →ₐ[R] C) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

theorem eq_zero_fibre (p : X ⟶ Spec (.of R)) [UniversallyClosed p] [GeometricallyIntegral p]
    (i : Spec (.of B) ⟶ X) [Flat i] [Surjective i] [QuasiCompact i] (f g : B →ₐ[R] C)
    (H : IsPullback (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) i i)
    (hφ : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B))) (r : B →ₐ[R] R)
    (k : Type) [Field k] [Algebra R k] (x : k ⊗[R] B)
    (hx : f.toLinearMap.baseChange k x = g.toLinearMap.baseChange k x)
    (hr : r.toLinearMap.baseChange k x = 0) : x = 0 := by
  let t : Spec (.of k) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R k))
  have hX := IsPullback.of_hasPullback p t
  have hB := isPullback_pr R k B
  have hC := isPullback_pr R k C
  let j : Spec (.of (k ⊗[R] B)) ⟶ pullback p t :=
    pullback.lift (prR R k B ≫ i) (prL R k B) (by rw [Category.assoc, hφ]; exact hB.w)
  have hj1 : j ≫ pullback.fst p t = prR R k B ≫ i := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd p t = prL R k B := pullback.lift_snd _ _ _
  have hj : IsPullback (prR R k B) j i (pullback.fst p t) :=
    IsPullback.of_bot (by rw [hj2, hφ]; exact hB) hj1.symm hX
  have hg : IsPullback (prR R k C) (Spec.map (bc k g)) (Spec.map (CommRingCat.ofHom g.toRingHom))
      (prR R k B) :=
    IsPullback.of_bot (by rw [bc_prL, specMap_algHom]; exact hC) (bc_prR k g).symm hB
  have hK : IsPullback (Spec.map (bc k f)) (Spec.map (bc k g)) j j := by
    refine IsPullback.of_right ?_ ?_ hj
    · rw [bc_prR, hj1]
      exact hg.paste_horiz H
    · apply pullback.hom_ext
      · simp only [Category.assoc, hj1]
        rw [← Category.assoc, ← Category.assoc, bc_prR, bc_prR, Category.assoc, Category.assoc, H.w]
      · simp only [Category.assoc, hj2, bc_prL]
  have : Flat j := MorphismProperty.of_isPullback hj ‹_›
  have : Surjective j := MorphismProperty.of_isPullback hj ‹_›
  have : QuasiCompact j := MorphismProperty.of_isPullback hj ‹_›
  have := ProperFunctions.isIso_appTop_of_field (pullback.snd p t)
  refine eq_zero_of_surjective (p := pullback.snd p t) (ConcreteCategory.bijective_of_isIso _).2
    j hK hj2 (bc k r) ?_ x ?_ ?_
  · have : Nontrivial (k ⊗[R] R) := (TensorProduct.rid R k).toEquiv.nontrivial
    exact RingHom.injective _
  · rw [bc_apply, bc_apply, hx]
  · rw [bc_apply, hr]

theorem isIso_appTop_of_cover (hI : FibreInjective) (hD : SmoothDescent)
    [Algebra.Smooth R B] [Algebra.Smooth R C]
    (p : X ⟶ Spec (.of R)) [UniversallyClosed p] [GeometricallyIntegral p]
    (i : Spec (.of B) ⟶ X) [Flat i] [Surjective i] [QuasiCompact i] (f g : B →ₐ[R] C)
    (H : IsPullback (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) i i)
    (hφ : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B))) (r : B →ₐ[R] R) :
    IsIso p.appTop := by
  let u := i.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom
  have h1 : ∀ c, u (p.appTop c) = algebraMap R B ((Scheme.ΓSpecIso (.of R)).hom c) :=
    fun c ↦ congr($(appTop_comp_eq hφ) c)
  have hu : Function.Injective u := by
    have h := FlatDescent.injective_appTop_of_epi i
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).hom).1.comp h
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun a b hab ↦ ?_, fun a ↦ ?_⟩
  · have h2 := (h1 a).symm.trans ((congrArg u hab).trans (h1 b))
    have h3 := congrArg r h2
    rw [r.commutes, r.commutes] at h3
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1 h3
  · have hfg : u ≫ CommRingCat.ofHom f.toRingHom = u ≫ CommRingCat.ofHom g.toRingHom := by
      simp only [u, Category.assoc]
      rw [← Scheme.ΓSpecIso_naturality, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Category.assoc, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, H.w]
    have hfg' : f (u a) = g (u a) := congr($hfg a)
    have h2 := eq_zero_of_fibres hI hD f g r (eq_zero_fibre p i f g H hφ r)
      (u a - algebraMap R B (r (u a)))
      (by rw [map_sub, map_sub, hfg', f.commutes, g.commutes])
      (by rw [map_sub, r.commutes]; exact sub_self _)
    refine ⟨(Scheme.ΓSpecIso (.of R)).inv (r (u a)), hu ?_⟩
    rw [h1, Iso.inv_hom_id_apply]
    exact (sub_eq_zero.mp h2).symm

end Core

section Main

variable {X S T : Scheme.{0}}

theorem isIso_appTop_of_section (hI : FibreInjective) (hD : SmoothDescent) (p : X ⟶ S)
    [IsAffine S] [Smooth p] [IsProper p] [GeometricallyIntegral p] (i : T ⟶ X) [IsAffine T]
    [Smooth i] [Surjective i] (s : S ⟶ T) (hs : s ≫ i ≫ p = 𝟙 S) : IsIso p.appTop := by
  have : IsAffineHom i := IsAffineHom.of_comp i p
  let Z := pullback i i
  have : IsAffine Z := isAffine_of_isAffineHom (pullback.fst i i)
  have h1 : (i ≫ p).appTop.hom.Smooth := by
    rw [← ProperFunctions.appLE_top_top _ le_top]
    exact (i ≫ p).smooth_appLE (isAffineOpen_top _) (isAffineOpen_top _) _
  have h2 : (pullback.fst i i ≫ i ≫ p).appTop.hom.Smooth := by
    rw [← ProperFunctions.appLE_top_top _ le_top]
    exact (pullback.fst i i ≫ i ≫ p).smooth_appLE (isAffineOpen_top _) (isAffineOpen_top _) _
  algebraize [(i ≫ p).appTop.hom, (pullback.fst i i ≫ i ≫ p).appTop.hom]
  let f : Γ(T, ⊤) →ₐ[Γ(S, ⊤)] Γ(Z, ⊤) :=
    { (pullback.fst i i).appTop.hom with
      commutes' := fun c ↦ congr($(Scheme.Hom.comp_appTop (pullback.fst i i) (i ≫ p)) c).symm }
  let g : Γ(T, ⊤) →ₐ[Γ(S, ⊤)] Γ(Z, ⊤) :=
    { (pullback.snd i i).appTop.hom with
      commutes' := fun c ↦ by
        have h := Scheme.Hom.comp_appTop (pullback.snd i i) (i ≫ p)
        rw [← pullback.condition_assoc] at h
        exact congr($h c).symm }
  let r : Γ(T, ⊤) →ₐ[Γ(S, ⊤)] Γ(S, ⊤) :=
    { s.appTop.hom with
      commutes' := fun c ↦ by
        have h := Scheme.Hom.comp_appTop s (i ≫ p)
        rw [hs, Scheme.Hom.id_appTop] at h
        exact congr($h c).symm }
  have : GeometricallyIntegral (p ≫ S.isoSpec.hom) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
      (IsPullback.of_horiz_isIso (fst := 𝟙 X) (f := p) (g := S.isoSpec.inv) ⟨by simp⟩) ‹_›
  have H : IsPullback (Spec.map (pullback.fst i i).appTop) (Spec.map (pullback.snd i i).appTop)
      (T.isoSpec.inv ≫ i) (T.isoSpec.inv ≫ i) :=
    (IsPullback.of_hasPullback i i).of_iso Z.isoSpec T.isoSpec T.isoSpec (.refl _)
      (Scheme.isoSpec_hom_naturality _).symm (Scheme.isoSpec_hom_naturality _).symm
      (by simp) (by simp)
  have hφ : (T.isoSpec.inv ≫ i) ≫ p ≫ S.isoSpec.hom = Spec.map (i ≫ p).appTop := by
    rw [Category.assoc, Iso.inv_comp_eq, Scheme.isoSpec_hom_naturality, Category.assoc]
  have := isIso_appTop_of_cover hI hD (R := Γ(S, ⊤)) (p ≫ S.isoSpec.hom) (T.isoSpec.inv ≫ i)
    f g H hφ r
  rw [Scheme.Hom.comp_appTop] at this
  have : IsIso S.isoSpec.hom.appTop := inferInstanceAs (IsIso (S.isoSpec.hom.app ⊤))
  exact IsIso.of_isIso_comp_left S.isoSpec.hom.appTop p.appTop

theorem isIso_appTop_of_isAffine (hI : FibreInjective) (hD : SmoothDescent) (p : X ⟶ S)
    [IsAffine S] [Smooth p] [IsProper p] [GeometricallyIntegral p] : IsIso p.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth)
  have : MorphismProperty.ContainsIdentities @Smooth.{0} := ⟨fun _ ↦ inferInstance⟩
  obtain ⟨T, i, _, hi, _⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @Smooth
  let j : pullback (i ≫ p) (i ≫ p) ⟶ pullback p (i ≫ p) :=
    pullback.lift (pullback.fst _ _ ≫ i) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have hj2 : j ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hj : IsPullback (pullback.fst _ _) j i (pullback.fst p (i ≫ p)) :=
    IsPullback.of_bot (by rw [hj2]; exact .of_hasPullback _ _) (pullback.lift_fst _ _ _).symm
      (.of_hasPullback _ _)
  have : Smooth j := MorphismProperty.of_isPullback hj ‹_›
  have : Surjective j := MorphismProperty.of_isPullback hj ‹_›
  have := isIso_appTop_of_section hI hD (pullback.snd p (i ≫ p)) j (pullback.diagonal (i ≫ p))
    (by rw [hj2, pullback.diagonal_snd])
  exact ProperFunctions.isIso_appTop_of_isPullback_of_surjective (.of_hasPullback p (i ≫ p))

theorem isIso_app (hI : FibreInjective) (hD : SmoothDescent) (p : X ⟶ S)
    [Smooth p] [IsProper p] [GeometricallyIntegral p] (U : S.Opens) : IsIso (p.app U) :=
  ProperFunctions.isIso_app_of_forall_affineOpens p (fun V ↦
    have : IsAffine V.1 := V.2
    isIso_appTop_of_isAffine hI hD (p ∣_ V.1)) U

end Main

theorem globalFns_of : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (R₀ R C₀ C₁ : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R] [AddCommGroup C₀] [Module R₀ C₀] [AddCommGroup C₁] [Module R₀ C₁] [Module.Flat R₀ C₀] [Module.Flat R₀ C₁] (φ : C₀ →ₗ[R₀] C₁), (∀ (k : Type) [Field k] [Algebra R k] [Algebra R₀ k] [IsScalarTower R₀ R k], Function.Injective (φ.baseChange k)) → Function.Injective (φ.baseChange R)) → (∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] (f g : B →ₐ[R] C) (r : B →ₐ[R] R), ∃ (R₀ B₀ C₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (_ : Algebra R₀ R) (_ : CommRing B₀) (_ : CommRing C₀) (_ : Algebra R₀ B₀) (_ : Algebra R₀ C₀) (f₀ g₀ : B₀ →ₐ[R₀] C₀) (r₀ : B₀ →ₐ[R₀] R₀) (β' : TensorProduct R₀ R B₀ ≃ₐ[R] B) (δ' : TensorProduct R₀ R C₀ ≃ₐ[R] C), Module.Flat R₀ B₀ ∧ Module.Flat R₀ C₀ ∧ ∀ b : B₀, f (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ f₀ b) ∧ g (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ g₀ b) ∧ r (β' (1 ⊗ₜ b)) = algebraMap R₀ R (r₀ b)) → GlobalFnsSt := by
  intro hG hI hD S A _ hA
  have := hA.smooth
  have := hA.proper
  have := hG _ _ A.hom hA.smooth hA.geomConnected
  have : IsIso A.hom.appTop := isIso_app hI hD A.hom ⊤
  exact ConcreteCategory.bijective_of_isIso A.hom.appTop

end GlobalFunctions

end GlobalTheory
