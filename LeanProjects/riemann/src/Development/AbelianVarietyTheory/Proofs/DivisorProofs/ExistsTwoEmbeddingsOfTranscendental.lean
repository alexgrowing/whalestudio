import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.CovTop

namespace GlobalTheory.ProjDrop

noncomputable def deg {A B : Type} [Field A] [Field B] (f : A →+* B) : ℕ :=
  @Module.finrank A B _ _ f.toAlgebra.toModule

theorem deg_comp {A B C : Type} [Field A] [Field B] [Field C] (f : A →+* B) (g : B →+* C) :
    deg (g.comp f) = deg f * deg g := by
  algebraize [f, g, g.comp f]
  exact (Module.finrank_mul_finrank A B C).symm

theorem deg_algebraMap (A B : Type) [Field A] [Field B] [i : Algebra A B] :
    deg (algebraMap A B) = Module.finrank A B := by
  have : (algebraMap A B).toAlgebra = i := Algebra.algebra_ext _ _ fun _ => rfl
  unfold deg
  rw [this]

theorem deg_equiv {A B : Type} [Field A] [Field B] (f : A ≃+* B) : deg (f : A →+* B) = 1 := by
  letI := (f : A →+* B).toAlgebra
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr f.bijective

theorem exists_compositum (B K₁ K₂ : Type) [Field B] [Field K₁] [Field K₂] (f₁ : B →+* K₁)
    (f₂ : B →+* K₂) (h₁ : deg f₁ ≠ 0) (h₂ : deg f₂ ≠ 0) :
    ∃ (Ω : Type) (_ : Field Ω) (j₁ : K₁ →+* Ω) (j₂ : K₂ →+* Ω),
      j₁.comp f₁ = j₂.comp f₂ ∧ deg (j₁.comp f₁) ≠ 0 := by
  algebraize [f₁, f₂]
  haveI : Module.Finite B K₁ := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h₁)
  haveI : Module.Finite B K₂ := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h₂)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct B K₁ K₂)
  letI := Ideal.Quotient.field m
  let a₁ : K₁ →ₐ[B] (TensorProduct B K₁ K₂ ⧸ m) :=
    (Ideal.Quotient.mkₐ B m).comp Algebra.TensorProduct.includeLeft
  let a₂ : K₂ →ₐ[B] (TensorProduct B K₁ K₂ ⧸ m) :=
    (Ideal.Quotient.mkₐ B m).comp Algebra.TensorProduct.includeRight
  have e₁ : a₁.toRingHom.comp f₁ = algebraMap B _ := a₁.comp_algebraMap
  have e₂ : a₂.toRingHom.comp f₂ = algebraMap B _ := a₂.comp_algebraMap
  refine ⟨TensorProduct B K₁ K₂ ⧸ m, inferInstance, a₁.toRingHom, a₂.toRingHom, e₁.trans e₂.symm, ?_⟩
  rw [e₁, deg_algebraMap]
  exact Module.finrank_pos.ne'

open IntermediateField Polynomial in
theorem not_mem_adjoin_sq {M K : Type} [Field M] [Field K] [Algebra M K] {t : K}
    (ht : Transcendental M t) : t ∉ M⟮t ^ 2⟯ := by
  rw [mem_adjoin_simple_iff]
  rintro ⟨r, s, h⟩
  have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ isAlgebraic_zero)
  have hs : aeval (t ^ 2) s ≠ 0 := fun h0 => ht0 (by rw [h, h0, div_zero])
  rw [eq_div_iff hs] at h
  have h2 : (X * expand M 2 s : M[X]) = expand M 2 r := by
    apply transcendental_iff_injective.mp ht
    simp only [map_mul, aeval_X, expand_aeval]
    exact h
  have hs0 : s ≠ 0 := fun h0 => hs (by simp [h0])
  have h3 := congrArg natDegree h2
  rw [natDegree_X_mul ((expand_ne_zero (by norm_num)).mpr hs0), natDegree_expand,
    natDegree_expand] at h3
  omega

open IntermediateField in

theorem exists_transcendental (F K : Type) [Field F] [Field K] [Algebra F K]
    [Algebra.EssFiniteType F K] (h : Module.finrank F K = 0) :
    ∃ (M : IntermediateField F K) (t : K), Transcendental M t ∧ Module.Finite M⟮t⟯ K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  have hne : Nonempty s := by
    by_contra hc
    haveI : IsEmpty s := not_nonempty_iff.mp hc
    haveI : Algebra.IsAlgebraic F K := hs.isEmpty_iff_isAlgebraic.mp inferInstance
    haveI : Module.Finite F K := Algebra.finite_of_essFiniteType_of_isAlgebraic
    exact Module.finrank_pos.ne' h
  obtain ⟨t⟩ := hne
  let M := adjoin F (((↑) : s → K) '' {t}ᶜ)
  refine ⟨M, t, transcendental_adjoin_iff.mpr (hs.1.transcendental_adjoin (by simp)), ?_⟩
  haveI : Algebra.EssFiniteType M K := Algebra.EssFiniteType.of_comp F _ K
  haveI : Algebra.EssFiniteType M⟮(t : K)⟯ K := Algebra.EssFiniteType.of_comp M _ K
  haveI : Algebra.IsAlgebraic M⟮(t : K)⟯ K := by
    have hle : Algebra.adjoin F (Set.range ((↑) : s → K)) ≤
        (M⟮(t : K)⟯.restrictScalars F).toSubalgebra := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨u, rfl⟩
      by_cases hu : u = t
      · subst hu
        exact mem_adjoin_simple_self M (u : K)
      · exact M⟮(t : K)⟯.algebraMap_mem ⟨u, subset_adjoin _ _ ⟨u, hu, rfl⟩⟩
    exact ⟨fun x => (hs.isAlgebraic.isAlgebraic x).tower_top_of_subalgebra_le hle⟩
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

open IntermediateField in

theorem exists_two_embeddings_of_transcendental {M K : Type} [Field M] [Field K] [Algebra M K]
    {t : K} (ht : Transcendental M t) (hfin : Module.Finite M⟮t⟯ K) :
    ∃ (Ω : Type) (_ : Field Ω) (j₁ j₂ : K →+* Ω),
      j₁.comp (algebraMap M K) = j₂.comp (algebraMap M K) ∧
      deg j₁ ≠ 0 ∧ deg j₂ ≠ 0 ∧ deg j₁ ≠ deg j₂ := by
  have ht2 : Transcendental M (t ^ 2) := ht.pow (by norm_num)
  let e : M⟮t ^ 2⟯ ≃ₐ[M] M⟮t⟯ :=
    (RatFunc.algEquivOfTranscendental _ ht2).symm.trans (RatFunc.algEquivOfTranscendental _ ht)
  have hle : M⟮t ^ 2⟯ ≤ M⟮t⟯ :=
    adjoin_simple_le_iff.mpr (pow_mem (mem_adjoin_simple_self M t) 2)
  let c : M⟮t ^ 2⟯ →+* M⟮t⟯ := (inclusion hle : M⟮t ^ 2⟯ →ₐ[M] M⟮t⟯)
  let b := algebraMap M⟮t⟯ K
  have hb : deg b ≠ 0 := by rw [deg_algebraMap]; exact Module.finrank_pos.ne'
  have hbc : b.comp c = algebraMap M⟮t ^ 2⟯ K := rfl
  have hfin2 : Module.Finite M⟮t ^ 2⟯ K := by
    have hi : IsIntegral M⟮t ^ 2⟯ t :=
      IsIntegral.of_pow (n := 2) (by norm_num)
        (isIntegral_algebraMap (x := AdjoinSimple.gen M (t ^ 2)))
    haveI := adjoin.finiteDimensional hi
    have hle' : M⟮t⟯ ≤ (M⟮t ^ 2⟯⟮t⟯).restrictScalars M :=
      adjoin_simple_le_iff.mpr (mem_adjoin_simple_self M⟮t ^ 2⟯ t)
    letI : Algebra M⟮t⟯ M⟮t ^ 2⟯⟮t⟯ := (inclusion hle').toRingHom.toAlgebra
    haveI : IsScalarTower M⟮t⟯ M⟮t ^ 2⟯⟮t⟯ K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite M⟮t ^ 2⟯⟮t⟯ K := Module.Finite.of_restrictScalars_finite M⟮t⟯ _ _
    exact Module.Finite.trans M⟮t ^ 2⟯⟮t⟯ K
  have h₁ : deg (b.comp c) ≠ 0 := by rw [hbc, deg_algebraMap]; exact Module.finrank_pos.ne'
  have h₂ : deg (b.comp (e.toRingEquiv : M⟮t ^ 2⟯ →+* M⟮t⟯)) = deg b := by
    rw [deg_comp, deg_equiv, one_mul]
  have hc : deg c ≠ 1 := by
    intro hc
    letI := c.toAlgebra
    obtain ⟨y, hy⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hc).2
      (AdjoinSimple.gen M t)
    have : (y : K) = t := congrArg Subtype.val hy
    have hy2 := y.2
    rw [this] at hy2
    exact not_mem_adjoin_sq ht hy2
  obtain ⟨Ω, _, j₁, j₂, hj, hd⟩ := exists_compositum _ K K _ _ h₁ (h₂.trans_ne hb)
  have hd' := congrArg deg hj
  rw [deg_comp _ j₁, deg_comp _ j₂, h₂, deg_comp, mul_comm (deg c), mul_assoc] at hd'
  have hd2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hb) hd'
  have k₁ : deg j₁ ≠ 0 := by
    rw [deg_comp] at hd
    exact right_ne_zero_of_mul hd
  have k₂ : deg j₂ ≠ 0 := by
    rw [hj, deg_comp] at hd
    exact right_ne_zero_of_mul hd
  refine ⟨Ω, inferInstance, j₁, j₂, ?_, k₁, k₂, fun hh => hc ?_⟩
  · ext x
    have h1 : (b.comp c) (algebraMap M _ x) = algebraMap M K x := rfl
    have h2 : (b.comp (e.toRingEquiv : M⟮t ^ 2⟯ →+* M⟮t⟯)) (algebraMap M _ x) =
        algebraMap M K x := (congrArg b (e.commutes x)).trans rfl
    have := RingHom.congr_fun hj (algebraMap M _ x)
    rw [RingHom.comp_apply, RingHom.comp_apply j₂, h1, h2] at this
    exact this
  · rw [← hh] at hd2
    exact (Nat.mul_eq_right k₁).mp hd2

theorem exists_two_embeddings {F K : Type} [Field F] [Field K] (φ : F →+* K)
    (hφ : φ.EssFiniteType) (h : deg φ = 0) :
    ∃ (Ω : Type) (_ : Field Ω) (j₁ j₂ : K →+* Ω), j₁.comp φ = j₂.comp φ ∧
      deg j₁ ≠ 0 ∧ deg j₂ ≠ 0 ∧ deg j₁ ≠ deg j₂ := by
  algebraize [φ]
  obtain ⟨M, t, ht, hfin⟩ := exists_transcendental F K h
  obtain ⟨Ω, _, j₁, j₂, hj, hd⟩ := exists_two_embeddings_of_transcendental ht hfin
  refine ⟨Ω, inferInstance, j₁, j₂, ?_, hd⟩
  ext x
  exact RingHom.congr_fun hj (algebraMap F M x)

theorem deg_eq_of_fieldPoint {W Y : Scheme.{0}} (g : W ⟶ Y) (w : W) (y : Y) {Ω : Type} [Field Ω]
    (ψ : W.residueField w ⟶ CommRingCat.of Ω) (j : Y.residueField y ⟶ CommRingCat.of Ω)
    (h : (Spec.map ψ ≫ W.fromSpecResidueField w) ≫ g = Spec.map j ≫ Y.fromSpecResidueField y) :
    g w = y ∧ deg j.hom = g.residueDegree w * deg ψ.hom := by
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Category.assoc, ← Spec.map_comp] at h
  have h' : (⟨g w, g.residueFieldMap w ≫ ψ⟩ :
      (y : Y) × (Y.residueField y ⟶ CommRingCat.of Ω)) = ⟨y, j⟩ :=
    (Scheme.SpecToEquivOfField Ω Y).symm.injective h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj h'
  obtain rfl := eq_of_heq h2
  exact ⟨rfl, deg_comp (g.residueFieldMap w).hom ψ.hom⟩

theorem charZero_of_residueField {W : Scheme.{0}} (w : W) [CharZero (W.residueField w)] :
    CharZero Γ(W, ⊤) :=
  (W.evaluation ⊤ w trivial).hom.charZero

theorem residueDegree_eq_zero {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral Y]
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D e : ℕ} (hX : IsArithVar p D) (hY : IsArithVar q e)
    (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hd : topologicalKrullDim (closure ({π (genericPoint Y)} : Set X)) <
      ((e + 1 : ℕ) : WithBot ℕ∞)) : π.residueDegree (genericPoint Y) = 0 := by
  by_contra hm
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (π (genericPoint Y))
  have hr : Set.range i = closure {π (genericPoint Y)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  haveI : Surjective (Limits.pullback.snd i π) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]
    exact Set.eq_univ_of_forall fun y =>
      ((genericPoint_specializes y).map π.continuous).mem_closure⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i π)
  obtain ⟨g, rfl⟩ : ∃ g : Y ⟶ Z, g ≫ i = π :=
    ⟨inv (Limits.pullback.snd i π) ≫ Limits.pullback.fst i π, by
      rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]⟩
  have hg : g (genericPoint Y) = genericPoint Z := i.isClosedEmbedding.injective hi.symm
  have hm' : g.residueDegree (genericPoint Y) ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp] at hm
    exact right_ne_zero_of_mul hm
  haveI := hY.flat
  haveI := DimCover.charZero_residueField (q ≫ spMap (Int.castRingHom k))
  haveI := (g.residueFieldMap (genericPoint Y)).hom.charZero
  have hc : CharZero Γ(Z, ⊤) := charZero_of_residueField (g (genericPoint Y))
  obtain ⟨d, hZ⟩ := hX.exists_dim_eq i
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero ?_
    rintro rfl
    exact hX.dim_ne_zero i hc hZ
  have hA := hX.of_isClosedImmersion i hc hZ
  have h1 := DimCover.topologicalKrullDim_eq k Z Y (i ≫ p) q d hA hY.isProjOver hY.flat g
    (by rw [← hπ, Category.assoc]) hg hm'
  have h2 : topologicalKrullDim (closure ({(g ≫ i) (genericPoint Y)} : Set X)) =
      topologicalKrullDim Z := by
    rw [← hr]
    exact (i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq _).symm
  rw [h2, hZ, ← h1, hY.dim_eq] at hd
  exact lt_irrefl _ hd

theorem exists_two_covers {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral Y]
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D e : ℕ} (hX : IsArithVar p D) (hY : IsArithVar q e)
    (π : Y ⟶ X) (hπ : π ≫ p = q) (h0 : π.residueDegree (genericPoint Y) = 0) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (p₁ p₂ : W ⟶ Y), p₁ ≫ π = p₂ ≫ π ∧
      IsArithVar (p₁ ≫ q) e ∧ p₁ (genericPoint W) = genericPoint Y ∧
      p₂ (genericPoint W) = genericPoint Y ∧ p₁.residueDegree (genericPoint W) ≠ 0 ∧
      p₂.residueDegree (genericPoint W) ≠ 0 ∧
      p₁.residueDegree (genericPoint W) ≠ p₂.residueDegree (genericPoint W) := by
  subst hπ
  haveI := CommonModel.isProper_of_isProjOver hX.isProjOver
  haveI := CommonModel.isProper_of_isProjOver hY.isProjOver
  haveI : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  obtain ⟨Ω, _, j₁, j₂, hj, k₁, k₂, k₃⟩ :=
    exists_two_embeddings (π.residueFieldMap (genericPoint Y)).hom
      (LocallyOfFiniteType.stalkMap π (genericPoint Y)).residueFieldMap h0
  let a₁ : Y.residueField (genericPoint Y) ⟶ CommRingCat.of Ω := CommRingCat.ofHom j₁
  let a₂ : Y.residueField (genericPoint Y) ⟶ CommRingCat.of Ω := CommRingCat.ofHom j₂
  have ha : π.residueFieldMap (genericPoint Y) ≫ a₁ = π.residueFieldMap (genericPoint Y) ≫ a₂ :=
    CommRingCat.hom_ext hj
  let c : Spec (CommRingCat.of Ω) ⟶ Limits.pullback π π :=
    Limits.pullback.lift (Spec.map a₁ ≫ Y.fromSpecResidueField _)
      (Spec.map a₂ ≫ Y.fromSpecResidueField _) (by
        simp only [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ha])
  obtain ⟨W, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (c (IsLocalRing.closedPoint Ω))
  have hc := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω _ c
  obtain ⟨e₁, d₁⟩ := deg_eq_of_fieldPoint (Limits.pullback.fst π π) _ _ _ a₁
    (by rw [hc]; exact Limits.pullback.lift_fst _ _ _)
  obtain ⟨e₂, d₂⟩ := deg_eq_of_fieldPoint (Limits.pullback.snd π π) _ _ _ a₂
    (by rw [hc]; exact Limits.pullback.lift_snd _ _ _)
  change deg j₁ = _ at d₁
  change deg j₂ = _ at d₂
  have r : ∀ g : Limits.pullback π π ⟶ Y, (i ≫ g).residueDegree (genericPoint W) =
      g.residueDegree (c (IsLocalRing.closedPoint Ω)) := fun g => by
    rw [CurveDegreesCompare.residueDegree_comp, Published.residueDegree_of_isClosedImmersion i, hi,
      mul_one]
  have g₁ : (i ≫ Limits.pullback.fst π π) (genericPoint W) = genericPoint Y := by
    rw [Scheme.Hom.comp_apply, hi, e₁]
  have g₂ : (i ≫ Limits.pullback.snd π π) (genericPoint W) = genericPoint Y := by
    rw [Scheme.Hom.comp_apply, hi, e₂]
  have n₁ : (i ≫ Limits.pullback.fst π π).residueDegree (genericPoint W) ≠ 0 := by
    rw [r]; rw [d₁] at k₁; exact left_ne_zero_of_mul k₁
  have n₂ : (i ≫ Limits.pullback.snd π π).residueDegree (genericPoint W) ≠ 0 := by
    rw [r]; rw [d₂] at k₂; exact left_ne_zero_of_mul k₂
  have hproj : IsProjOver ((i ≫ Limits.pullback.fst π π) ≫ π ≫ p) := by
    have := ProjSpace.isProjOver_comp_of_isClosedImmersion (i ≫ Limits.pullback.mapDesc π π p)
      (ProjSpace.isProjOver_pullback hY.isProjOver hY.isProjOver)
    have e : Limits.pullback.mapDesc π π p ≫ Limits.pullback.fst (π ≫ p) (π ≫ p) =
        Limits.pullback.fst π π := (Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _)
    rw [Category.assoc, ← Category.assoc (Limits.pullback.mapDesc π π p), e] at this
    rwa [Category.assoc]
  have hflat : Flat (((i ≫ Limits.pullback.fst π π) ≫ π ≫ p) ≫ spMap (Int.castRingHom k)) := by
    rw [flat_int_iff_charZero]
    haveI := hY.flat
    haveI : CharZero (Y.residueField ((i ≫ Limits.pullback.fst π π) (genericPoint W))) :=
      g₁.symm ▸ DimCover.charZero_residueField ((π ≫ p) ≫ spMap (Int.castRingHom k))
    haveI := (RingHom.charZero_iff
      ((i ≫ Limits.pullback.fst π π).residueFieldMap (genericPoint W)).hom.injective).mp this
    exact charZero_of_residueField (genericPoint W)
  refine ⟨W, inferInstance, i ≫ Limits.pullback.fst π π, i ≫ Limits.pullback.snd π π, ?_,
    ⟨hY.isDomain, hY.finite, inferInstance, hproj, hflat,
      DimCover.topologicalKrullDim_eq k Y W _ _ e hY hproj hflat _ rfl g₁ n₁⟩,
    g₁, g₂, n₁, n₂, ?_⟩
  · rw [Category.assoc, Category.assoc, Limits.pullback.condition]
  · rw [r, r]
    intro hh
    exact k₃ (by rw [d₁, d₂, hh])

theorem isSelfInter_zero_of_dim_lt : GlobalTheory.Published.ArCalc →
    ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
      (D e : ℕ), IsArithVar p D → IsArithVar q e → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q),
      topologicalKrullDim (closure ({π (genericPoint Y)} : Set X)) < ((e + 1 : ℕ) : WithBot ℕ∞) →
      ∀ L : HermLB p, (L.pull π hπ).IsSelfInter 0 := by
  intro H k _ X Y _ p q D e hX hY π hπ hd L
  obtain ⟨W, _, p₁, p₂, hp, hW, g₁, g₂, n₁, n₂, hne⟩ :=
    exists_two_covers hX hY π hπ (residueDegree_eq_zero hX hY π hπ hd)
  obtain ⟨h, hh⟩ := (H.arExists k Y q e hY).1 (L.pull π hπ)
  have ha : (L.pull π hπ).IsSelfInter (h (genericPoint Y)) := ⟨h, hh, rfl⟩
  have hq : p₂ ≫ q = p₁ ≫ q := by rw [← hπ, ← Category.assoc, ← hp, Category.assoc]
  have key : ∀ (g : W ⟶ Y) (hg : g ≫ q = p₁ ≫ q) (r : W ⟶ X) (hr : r ≫ p = p₁ ≫ q),
      g ≫ π = r → g (genericPoint W) = genericPoint Y → g.residueDegree (genericPoint W) ≠ 0 →
      (L.pull r hr).IsSelfInter (g.residueDegree (genericPoint W) * h (genericPoint Y)) := by
    rintro g hg _ hr rfl h1 h2
    obtain ⟨f, hf, hf'⟩ := (H.arProj k Y W q _ e hY hW g hg h1 h2).1 _ _ ha
    exact ⟨f, (L.refines_pull_pull π hπ g hg hr).isArithHeight hW hf, hf'⟩
  have hr : (p₁ ≫ π) ≫ p = p₁ ≫ q := by rw [Category.assoc, hπ]
  have := HermLB.IsSelfInter.unique hW (key p₁ rfl _ hr rfl g₁ n₁) (key p₂ hq _ hr hp.symm g₂ n₂)
  rcases mul_eq_mul_right_iff.mp this with h1 | h1
  · exact absurd (Nat.cast_injective h1) hne
  · exact h1 ▸ ha

theorem isSelfInter_zero_of_classicalTheorems : Hypotheses2 →
    ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
      (D e : ℕ), IsArithVar p D → IsArithVar q e → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q),
      topologicalKrullDim (closure ({π (genericPoint Y)} : Set X)) < ((e + 1 : ℕ) : WithBot ℕ∞) →
      ∀ L : HermLB p, (L.pull π hπ).IsSelfInter 0 :=
  fun P => isSelfInter_zero_of_dim_lt P.p4

end GlobalTheory.ProjDrop
