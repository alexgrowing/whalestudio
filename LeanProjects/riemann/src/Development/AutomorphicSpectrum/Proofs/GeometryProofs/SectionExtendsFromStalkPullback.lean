import Mathlib
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ggeo.LocalLift

theorem exists_mul_eq_of_isPushout {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (po : IsPushout f g h k) (M : Submonoid A)
    (hg : ∀ c : C, ∃ a, ∃ m ∈ M, c * g.hom m = g.hom a) (d : D) :
    ∃ m ∈ M, ∃ b, d * h.hom (f.hom m) = h.hom b := by
  have GlobalTheory.CompanionTheory.Ar.Conj.hw : ∀ a, h.hom (f.hom a) = k.hom (g.hom a) := fun a => by
    have := congrArg (fun φ : A ⟶ D => φ.hom a) po.w
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have GlobalTheory.CompanionTheory.RedCov.Levi.hd : d ∈ Subring.closure
      (Set.range (ConcreteCategory.hom h) ∪ Set.range (ConcreteCategory.hom k)) := by
    rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout po]
    exact Subring.mem_top d
  refine Subring.closure_induction
    (p := fun x _ => ∃ m ∈ M, ∃ b, x * h.hom (f.hom m) = h.hom b) ?_ ?_ ?_ ?_ ?_ ?_ GlobalTheory.CompanionTheory.RedCov.Levi.hd
  · rintro x (⟨b, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨1, M.one_mem, b, ?_⟩
      show h.hom b * h.hom (f.hom 1) = h.hom b
      simp
    · show ∃ m ∈ M, ∃ b, k.hom c * h.hom (f.hom m) = h.hom b
      obtain ⟨a, m, hm, hca⟩ := hg c
      refine ⟨m, hm, f.hom a, ?_⟩
      rw [GlobalTheory.CompanionTheory.Ar.Conj.hw, GlobalTheory.CompanionTheory.Ar.Conj.hw, ← map_mul, hca]
  · exact ⟨1, M.one_mem, 0, by simp⟩
  · exact ⟨1, M.one_mem, 1, by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨m₁, hm₁, b₁, e₁⟩ := hx
    obtain ⟨m₂, hm₂, b₂, e₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, b₁ * f.hom m₂ + b₂ * f.hom m₁, ?_⟩
    simp only [map_mul, map_add]
    linear_combination h.hom (f.hom m₂) * e₁ + h.hom (f.hom m₁) * e₂
  · intro x _ hx
    obtain ⟨m, hm, b, e⟩ := hx
    exact ⟨m, hm, -b, by rw [neg_mul, e, map_neg]⟩
  · intro x y _ _ hx hy
    obtain ⟨m₁, hm₁, b₁, e₁⟩ := hx
    obtain ⟨m₂, hm₂, b₂, e₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, b₁ * b₂, ?_⟩
    simp only [map_mul]
    linear_combination (y * h.hom (f.hom m₂)) * e₁ + h.hom b₁ * e₂

theorem stalk_exists_mul_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U)
    (c : X.presheaf.stalk p) :
    ∃ a m : Γ(X, U), IsUnit ((X.presheaf.germ U p hp).hom m) ∧
      c * (X.presheaf.germ U p hp).hom m = (X.presheaf.germ U p hp).hom a := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
  have hloc := hU.isLocalization_stalk ⟨p, hp⟩
  obtain ⟨⟨a, m⟩, hm⟩ := @IsLocalization.surj _ _ _ _ _ _ hloc c
  exact ⟨a, m, @IsLocalization.map_units _ _ _ _ _ _ hloc m, hm⟩

theorem fromSpecStalk_appLE {X : Scheme.{0}} {U : X.Opens} {p : X} (hp : p ∈ U)
    (h : (⊤ : (Spec (X.presheaf.stalk p)).Opens) ≤ X.fromSpecStalk p ⁻¹ᵁ U) :
    (X.fromSpecStalk p).appLE U ⊤ h =
      X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso (X.presheaf.stalk p)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hp, Category.assoc, Category.assoc,
    ← Functor.map_comp]
  have e : (homOfLE (le_top : X.fromSpecStalk p ⁻¹ᵁ U ≤ ⊤)).op ≫ (homOfLE h).op =
      𝟙 (Opposite.op (⊤ : (Spec (X.presheaf.stalk p)).Opens)) := by
    first
    | exact Subsingleton.elim _ _
    | rfl
  rw [e]
  exact (congrArg (fun t => X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso (X.presheaf.stalk p)).inv ≫ t)
    ((Spec (X.presheaf.stalk p)).presheaf.map_id _)).trans (by simp only [Category.comp_id])

theorem exists_extension {X Y Z P : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y) (hy : π y₀ = p)
    (fst : P ⟶ Y) (snd : P ⟶ Spec (X.presheaf.stalk p))
    (H : IsPullback fst snd π (X.fromSpecStalk p)) (c : Z ⟶ P) [IsClosedImmersion c]
    (s : Γ(Z, ⊤)) :
    ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧ ((c ≫ fst).app W).hom f =
      Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ W ≤ ⊤)).op s := by
  obtain ⟨V, hV, hpV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := p) (by simp)
  have hy₀ : y₀ ∈ π ⁻¹ᵁ V := (Scheme.Hom.mem_preimage π).2 (by rw [hy]; exact hpV)
  obtain ⟨W₀, hW₀, hy₀W₀, hW₀V⟩ := exists_isAffineOpen_mem_and_subset hy₀
  have hUSX : W₀ ≤ π ⁻¹ᵁ V := fun x hx => hW₀V hx
  have hUST : (⊤ : (Spec (X.presheaf.stalk p)).Opens) ≤ X.fromSpecStalk p ⁻¹ᵁ V := by
    intro x _
    have hx : X.fromSpecStalk p x ∈ Set.range (X.fromSpecStalk p) := ⟨x, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hx
    have hx' : X.fromSpecStalk p x ⤳ p := hx
    exact (Scheme.Hom.mem_preimage _).2 (Specializes.mem_open hx' V.isOpen hpV)
  obtain ⟨UY, hUY⟩ : ∃ UY, UY = fst ⁻¹ᵁ W₀ ⊓ snd ⁻¹ᵁ ⊤ := ⟨_, rfl⟩
  have hUYle : UY ≤ fst ⁻¹ᵁ W₀ := by
    rw [hUY]
    exact inf_le_left
  have hpo := (isIso_pushoutSection_iff H hUST hUSX hUY).1
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hV (isAffineOpen_top _) hW₀)
  have hUYaff : IsAffineOpen UY := by
    have hpb := Scheme.Hom.isPullback_resLE H hUST hUSX hUY
    haveI : IsAffine (W₀ : Scheme.{0}) := hW₀
    haveI : IsAffine (V : Scheme.{0}) := hV
    haveI : IsAffine ((⊤ : (Spec (X.presheaf.stalk p)).Opens) : Scheme.{0}) :=
      isAffineOpen_top _
    haveI := Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      (π.resLE V W₀ hUSX) ((X.fromSpecStalk p).resLE V ⊤ hUST)
    exact IsAffine.of_isIso hpb.isoPullback.hom
  obtain ⟨d, GlobalTheory.CompanionTheory.RedCov.Levi.hd⟩ := Scheme.Hom.app_surjective c UY hUYaff
    ((Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op).hom s)
  have hd' : (c.app UY).hom d = (Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op).hom s :=
    GlobalTheory.CompanionTheory.RedCov.Levi.hd
  have hg : ∀ c' : Γ(Spec (X.presheaf.stalk p), ⊤), ∃ a, ∃ m ∈
      (IsUnit.submonoid (X.presheaf.stalk p)).comap (X.presheaf.germ V p hpV).hom,
      c' * ((X.fromSpecStalk p).appLE V ⊤ hUST).hom m =
        ((X.fromSpecStalk p).appLE V ⊤ hUST).hom a := by
    intro c'
    obtain ⟨a, m, hmu, hm⟩ := GlobalTheory.CompanionTheory.Ggeo.LocalLift.stalk_exists_mul_eq hV hpV
      ((Scheme.ΓSpecIso (X.presheaf.stalk p)).hom.hom c')
    refine ⟨a, m, Submonoid.mem_comap.2 ((IsUnit.mem_submonoid_iff _).2 hmu), ?_⟩
    rw [GlobalTheory.CompanionTheory.Ggeo.LocalLift.fromSpecStalk_appLE hpV, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply,
      ← hm, map_mul]
    exact congrArg (fun t => t * _) (CommRingCat.inv_hom_apply _ c').symm
  obtain ⟨m, hmM, b, hb⟩ := GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_mul_eq_of_isPushout hpo _ hg d
  have hmu : IsUnit ((X.presheaf.germ V p hpV).hom m) :=
    (IsUnit.mem_submonoid_iff _).1 (Submonoid.mem_comap.1 hmM)
  have hy₀W : y₀ ∈ Y.basicOpen ((π.appLE V W₀ hUSX).hom m) := by
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.basicOpen_res]
    refine TopologicalSpace.Opens.mem_inf.2 ⟨hy₀W₀, ?_⟩
    rw [← Scheme.preimage_basicOpen, Scheme.Hom.mem_preimage, hy]
    exact (X.mem_basicOpen m p hpV).2 hmu
  obtain ⟨fm, hfm⟩ : ∃ fm, (π.appLE V W₀ hUSX).hom m = fm := ⟨_, rfl⟩
  rw [hfm] at hb hy₀W
  have hWW₀ : Y.basicOpen fm ≤ W₀ := Y.basicOpen_le fm
  have hu : IsUnit ((Y.presheaf.map (homOfLE hWW₀).op).hom fm) :=
    RingedSpace.isUnit_res_basicOpen _ fm
  refine ⟨Y.basicOpen fm, (Y.presheaf.map (homOfLE hWW₀).op).hom b * ↑hu.unit⁻¹, hy₀W, ?_⟩
  have hQ : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ c ⁻¹ᵁ UY := by
    rw [hUY]
    intro z hz
    exact (Scheme.Hom.mem_preimage c).2 (TopologicalSpace.Opens.mem_inf.2
      ⟨(Scheme.Hom.mem_preimage fst).2 (hWW₀ ((Scheme.Hom.mem_preimage (c ≫ fst)).1 hz)),
        (Scheme.Hom.mem_preimage snd).2 (by simp)⟩)
  have E₁ : Y.presheaf.map (homOfLE hWW₀).op ≫ (c ≫ fst).app (Y.basicOpen fm) =
      fst.appLE W₀ UY hUYle ≫ c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
  have e₁ : ∀ x, ((c ≫ fst).app (Y.basicOpen fm)).hom
      ((Y.presheaf.map (homOfLE hWW₀).op).hom x) =
      (c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ).hom ((fst.appLE W₀ UY hUYle).hom x) := by
    intro x
    have := congrArg (fun φ => CommRingCat.Hom.hom φ x) E₁
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have E₂ : Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op ≫
      Z.presheaf.map (homOfLE hQ).op =
      Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ ⊤)).op := by
    (rw [← Functor.map_comp]) <;> rfl
  have e₂ : (c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ).hom d =
      (Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ ⊤)).op).hom s := by
    have h₂ := congrArg (fun φ => CommRingCat.Hom.hom φ s) E₂
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h₂
    rw [← h₂, ← hd', Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [map_mul, e₁ b, ← hb, map_mul, e₂, ← e₁ fm, mul_assoc, ← map_mul, hu.mul_val_inv,
    map_one, mul_one]

theorem exists_open_extension : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y), π y₀ = p →
    ∀ (c : Z ⟶ pullback π (X.fromSpecStalk p)) [IsClosedImmersion c] (s : Γ(Z, ⊤)),
    ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧
      ((c ≫ pullback.fst π (X.fromSpecStalk p)).app W).hom f =
        Z.presheaf.map (homOfLE (le_top : (c ≫ pullback.fst π (X.fromSpecStalk p)) ⁻¹ᵁ W ≤ ⊤)).op s := by
  intro X Y Z π p y₀ hy c _ s
  exact exists_extension π p y₀ hy _ _ (IsPullback.of_hasPullback π (X.fromSpecStalk p)) c s

end GlobalTheory.CompanionTheory.Ggeo.LocalLift
