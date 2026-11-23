import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GrpDense

variable {Z U : Scheme.{0}} {j : U ⟶ Z}

theorem exists_generic [IsIntegral Z] [Nonempty U] (j : U ⟶ Z) [IsOpenImmersion j] :
    ∃ (W : Scheme.{0}) (k : W ⟶ U), QuasiCompact (k ≫ j) ∧ IsSchemeTheoreticallyDominant (k ≫ j) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  refine ⟨Spec U.functionField, U.fromSpecStalk (genericPoint U), ?_, ?_⟩
  · constructor
    intro s _ _
    have : Subsingleton (Spec U.functionField) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum U.functionField))
    exact Set.subsingleton_of_subsingleton.isCompact
  · have hk : DenseRange (U.fromSpecStalk (genericPoint U)) := by
      refine Dense.mono ?_ (dense_iff_closure_eq.mpr (isGenericPoint_def.mp (genericPoint_spec U)))
      rintro _ rfl
      rw [Scheme.range_fromSpecStalk]
      exact specializes_refl _
    have hj : DenseRange j :=
      (Scheme.Hom.isOpenEmbedding j).isOpen_range.dense (Set.range_nonempty _)
    have : IsDominant (U.fromSpecStalk (genericPoint U)) := ⟨hk⟩
    have : IsDominant j := ⟨hj⟩
    exact IsSchemeTheoreticallyDominant.of_isDominant _

theorem hom_ext_of_points [IsIntegral Z] [Nonempty U] (j : U ⟶ Z) [IsOpenImmersion j] {X Y : Over Z} [Flat X.hom]
    [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  obtain ⟨W, k, hqc, hstd⟩ := exists_generic j
  have := hqc
  have := hstd
  apply Over.OverMorphism.ext
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant Y.hom (by simp) (pullback.fst X.hom (k ≫ j)) ?_
  have := h (Over.mk (pullback.snd X.hom (k ≫ j) ≫ k))
    (Over.homMk (pullback.fst X.hom (k ≫ j)) (by simpa using pullback.condition))
  simpa using congrArg (fun t => t.left) this

variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}

theorem pushPt_surjective (h : IsPullback φ A.hom G.hom j) (T : Over U) (x₀ : Over.mk (T.hom ≫ j) ⟶ G) :
    ∃ x : T ⟶ A, pushPt h.w x = x₀ := by
  refine ⟨Over.homMk (h.lift x₀.left T.hom (by simp)) (h.lift_snd _ _ _), ?_⟩
  apply Over.OverMorphism.ext
  exact h.lift_fst _ _ _

variable [GrpObj A] (w : φ ≫ G.hom = A.hom ≫ j)

theorem pushPt_mul {m : G ⊗ G ⟶ G}
    (hm : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    {T : Over U} (x y : T ⟶ A) : lift (pushPt w x) (pushPt w y) ≫ m = pushPt w (x * y) := by
  have hsq : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ (lift (pushPt w (fst A A)) (pushPt w (snd A A))).left := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare
    constructor
    · rw [← Over.comp_left, lift_fst]
      rfl
    · rw [← Over.comp_left, lift_snd]
      rfl
  have key := hm _ hsq
  have hL : lift (pushPt w x) (pushPt w y) =
      Over.homMk (U := Over.mk (T.hom ≫ j)) (V := Over.mk ((A ⊗ A).hom ≫ j)) (lift x y).left
        (by
          show (lift x y).left ≫ ((A ⊗ A).hom ≫ j) = T.hom ≫ j
          rw [← Category.assoc, Over.w]) ≫
        lift (pushPt w (fst A A)) (pushPt w (snd A A)) := by
    apply hom_ext
    · rw [lift_fst, Category.assoc, lift_fst]
      apply Over.OverMorphism.ext
      change x.left ≫ φ = (lift x y).left ≫ (fst A A).left ≫ φ
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · rw [lift_snd, Category.assoc, lift_snd]
      apply Over.OverMorphism.ext
      change y.left ≫ φ = (lift x y).left ≫ (snd A A).left ≫ φ
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  apply Over.OverMorphism.ext
  rw [hL, Over.comp_left, Over.comp_left, Category.assoc, key]
  change (lift x y).left ≫ (μ[A]).left ≫ φ = (x * y).left ≫ φ
  rw [Hom.mul_def, Over.comp_left, Category.assoc]

theorem pushPt_inv {i : G ⟶ G} (hi : φ ≫ i.left = (ι[A]).left ≫ φ) {T : Over U} (x : T ⟶ A) :
    pushPt w x ≫ i = pushPt w x⁻¹ := by
  apply Over.OverMorphism.ext
  change (x.left ≫ φ) ≫ i.left = (x⁻¹).left ≫ φ
  rw [Category.assoc, hi, Hom.inv_def, Over.comp_left, Category.assoc]

theorem pushPt_one {e : 𝟙_ (Over Z) ⟶ G} (he : j ≫ e.left = (η[A]).left ≫ φ) (T : Over U) :
    toUnit _ ≫ e = pushPt w (1 : T ⟶ A) := by
  apply Over.OverMorphism.ext
  change (toUnit (Over.mk (T.hom ≫ j))).left ≫ e.left = (1 : T ⟶ A).left ≫ φ
  rw [Hom.one_def, Over.comp_left, Category.assoc, ← he]
  have h1 : (toUnit (Over.mk (T.hom ≫ j))).left = T.hom ≫ j := by
    simp
  have h2 : (toUnit T).left = T.hom := by
    simp
  rw [h1, h2, Category.assoc]

end GlobalTheory.GrpDense

namespace GlobalTheory

open GrpDense

theorem grpObj_of_dense_open :
    ∀ (Z U : Scheme.{0}) [IsIntegral Z] [Nonempty U] (j : U ⟶ Z) [IsOpenImmersion j] (G : Over Z) [Smooth G.hom]
      [IsSeparated G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left),
      IsPullback φ A.hom G.hom j → ∀ (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G),
      (∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) →
      φ ≫ i.left = (ι[A]).left ≫ φ → j ≫ e.left = (η[A]).left ≫ φ →
      ∃ _ : GrpObj G, μ[G] = m ∧ η[G] = e ∧ ι[G] = i ∧ IsCommMonObj G ∧ IsGrpPullback A G j φ := by
  intro Z U _ _ j _ G _ _ A _ _ φ h m i e hm hi he
  have : Flat G.hom := inferInstance
  have : Flat (𝟙_ (Over Z)).hom := GlobalTheory.ExtUnique.flat_tensorUnit
  have : Flat (G ⊗ G).hom := GlobalTheory.ExtUnique.flat_tensorObj G G
  have : Flat ((G ⊗ G) ⊗ G).hom := GlobalTheory.ExtUnique.flat_tensorObj (G ⊗ G) G
  have : Flat (𝟙_ (Over Z) ⊗ G).hom := GlobalTheory.ExtUnique.flat_tensorObj _ G
  have : Flat (G ⊗ 𝟙_ (Over Z)).hom := GlobalTheory.ExtUnique.flat_tensorObj G _
  have hext : ∀ {X : Over Z} [Flat X.hom] (f g : X ⟶ G),
      (∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) → f = g :=
    fun f g H => hom_ext_of_points j H
  have mulP : ∀ {T : Over U} (x y : T ⟶ A),
      lift (pushPt h.w x) (pushPt h.w y) ≫ m = pushPt h.w (x * y) :=
    fun x y => pushPt_mul h.w hm x y
  have invP : ∀ {T : Over U} (x : T ⟶ A), pushPt h.w x ≫ i = pushPt h.w x⁻¹ :=
    fun x => pushPt_inv h.w hi x
  have oneP : ∀ (T : Over U), toUnit _ ≫ e = pushPt h.w (1 : T ⟶ A) :=
    fun T => pushPt_one h.w he T
  have surj := pushPt_surjective h
  letI inst : GrpObj G :=
    { one := e
      mul := m
      inv := i
      one_mul := by
        apply hext
        intro T t
        obtain ⟨y, hy⟩ := surj T (t ≫ snd _ _)
        have ht : t = lift (toUnit _) (pushPt h.w y) :=
          hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hy])
        rw [ht]
        simp only [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        rw [oneP, mulP, _root_.one_mul]
      mul_one := by
        apply hext
        intro T t
        obtain ⟨x, hx⟩ := surj T (t ≫ fst _ _)
        have ht : t = lift (pushPt h.w x) (toUnit _) :=
          hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        rw [ht]
        simp only [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        rw [oneP, mulP, _root_.mul_one]
      mul_assoc := by
        apply hext
        intro T t
        obtain ⟨x, hx⟩ := surj T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := surj T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := surj T (t ≫ snd _ _)
        have ht : t = lift (lift (pushPt h.w x) (pushPt h.w y)) (pushPt h.w z) := by
          refine hom_ext _ _ ?_ (by rw [lift_snd, hz])
          rw [lift_fst]
          exact hom_ext _ _ (by rw [lift_fst, hx, Category.assoc]) (by rw [lift_snd, hy, Category.assoc])
        rw [ht]
        simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
          mulP, _root_.mul_assoc]
      left_inv := by
        apply hext
        intro T t
        obtain ⟨x, rfl⟩ := surj T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, invP, mulP, _root_.inv_mul_cancel, oneP]
      right_inv := by
        apply hext
        intro T t
        obtain ⟨x, rfl⟩ := surj T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc, invP, mulP, _root_.mul_inv_cancel, oneP] }
  refine ⟨inst, rfl, rfl, rfl, ⟨?_⟩, ?_⟩
  · change (β_ G G).hom ≫ m = m
    apply hext
    intro T t
    obtain ⟨x, hx⟩ := surj T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := surj T (t ≫ snd _ _)
    have ht : t = lift (pushPt h.w x) (pushPt h.w y) :=
      hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])
    rw [ht, lift_braiding_hom_assoc, mulP, mulP, _root_.mul_comm]
  · unfold IsGrpPullback
    refine ⟨h, ?_⟩
    intro T x y x₀ y₀ hx hy
    have e₀ : x₀ = pushPt h.w x := Over.OverMorphism.ext hx
    have e₁ : y₀ = pushPt h.w y := Over.OverMorphism.ext hy
    subst e₀ e₁
    rw [Hom.mul_def]
    exact congrArg (fun t => t.left) (mulP x y)

end GlobalTheory
