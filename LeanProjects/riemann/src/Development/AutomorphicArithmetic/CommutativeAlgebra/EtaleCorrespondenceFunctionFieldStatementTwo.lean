import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsSeparatedOfProj
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFunctionFieldStatementOne
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

open scoped TensorProduct in
open CategoryTheory.Limits in
private theorem surj_productMap {Y : Scheme.{0}} [Y.IsSeparated] {A B C : CommRingCat.{0}} (f1 : Spec A ⟶ Y) (f2 : Spec B ⟶ Y)
    (r1 : A ⟶ C) (r2 : B ⟶ C) (pb : IsPullback (Spec.map r1) (Spec.map r2) f1 f2) :
    Function.Surjective (Algebra.TensorProduct.productMap r1.hom.toIntAlgHom r2.hom.toIntAlgHom) := by
  let i : Y ⟶ Spec (.of ℤ) := specZIsTerminal.from Y
  have e1 : f1 ≫ i = Spec.map (CommRingCat.ofHom (algebraMap ℤ A)) := specZIsTerminal.hom_ext _ _
  have e2 : f2 ≫ i = Spec.map (CommRingCat.ofHom (algebraMap ℤ B)) := specZIsTerminal.hom_ext _ _
  let φ : A ⊗[ℤ] B →+* C := (Algebra.TensorProduct.productMap r1.hom.toIntAlgHom r2.hom.toIntAlgHom).toRingHom
  let J : Spec C ⟶ Spec (.of (A ⊗[ℤ] B)) :=
    pb.isoPullback.hom ≫ pullback.mapDesc f1 f2 i ≫ (pullback.congrHom e1 e2).hom ≫ (pullbackSpecIso ℤ A B).hom
  have hJ : IsClosedImmersion J := inferInstance
  have hφ1 : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := B)) ≫ CommRingCat.ofHom φ = r1 := by
    ext a
    simp [φ]
  have hφ2 : CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := B)).toRingHom ≫ CommRingCat.ofHom φ = r2 := by
    ext b
    simp [φ]
  have q1 : pullback.mapDesc f1 f2 i ≫ (pullback.congrHom e1 e2).hom ≫ pullback.fst _ _ = pullback.fst f1 f2 := by
    simp only [pullback.mapDesc, pullback.congrHom_hom, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  have q2 : pullback.mapDesc f1 f2 i ≫ (pullback.congrHom e1 e2).hom ≫ pullback.snd _ _ = pullback.snd f1 f2 := by
    simp only [pullback.mapDesc, pullback.congrHom_hom, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have hJe : J = Spec.map (CommRingCat.ofHom φ) := by
    rw [← cancel_mono (pullbackSpecIso ℤ A B).inv]
    apply pullback.hom_ext
    · simp only [J, Category.assoc, Iso.hom_inv_id, Category.comp_id, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      rw [hφ1, q1, pb.isoPullback_hom_fst]
    · simp only [J, Category.assoc, Iso.hom_inv_id, Category.comp_id, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      rw [q2, pb.isoPullback_hom_snd, ← hφ2]
      rfl
  rw [hJe] at hJ
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map (CommRingCat.ofHom φ))).2
  have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  intro c
  obtain ⟨t, ht⟩ := hs ((Scheme.ΓSpecIso C).inv.hom c)
  refine ⟨(Scheme.ΓSpecIso (.of (A ⊗[ℤ] B))).hom.hom t, ?_⟩
  have h3 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (.of (A ⊗[ℤ] B))).hom.hom t)) nat
  simp only [CommRingCat.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply] at h3
  have h4 : (Scheme.ΓSpecIso (.of (A ⊗[ℤ] B))).inv.hom ((Scheme.ΓSpecIso (.of (A ⊗[ℤ] B))).hom.hom t) = t := by
    simp
  rw [h4] at h3
  have h5 := (ConcreteCategory.injective_of_mono_of_preservesPullback (Scheme.ΓSpecIso C).inv)
  exact h5 (h3.trans ht)

private theorem pb_aff {Y : Scheme.{0}} [Y.IsSeparated] {W1 W2 : Y.Opens} (h1 : IsAffineOpen W1) (h2 : IsAffineOpen W2) :
    IsPullback (Spec.map (Y.presheaf.map (homOfLE (inf_le_left : W1 ⊓ W2 ≤ W1)).op))
      (Spec.map (Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op)) h1.fromSpec h2.fromSpec := by
  have h12 : IsAffineOpen (W1 ⊓ W2) := h1.inf h2
  have ha := h1.map_fromSpec h12 (homOfLE (inf_le_left : W1 ⊓ W2 ≤ W1)).op
  have hb := h2.map_fromSpec h12 (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op
  haveI : IsOpenImmersion (Spec.map (Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op)) := by
    have : IsOpenImmersion (Spec.map (Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op) ≫ h2.fromSpec) := by
      rw [hb]; infer_instance
    exact IsOpenImmersion.of_comp _ h2.fromSpec
  refine IsOpenImmersion.isPullback _ _ _ _ (hb.trans ha.symm) ?_
  refine TopologicalSpace.Opens.ext (Set.ext fun z => ⟨fun hz => ?_, ?_⟩)
  · have hz1 : h2.fromSpec z ∈ W1 := by
      have : h2.fromSpec z ∈ Set.range h1.fromSpec := hz
      rwa [h1.range_fromSpec] at this
    have hz2 : h2.fromSpec z ∈ W2 := by
      have : h2.fromSpec z ∈ Set.range h2.fromSpec := ⟨z, rfl⟩
      rwa [h2.range_fromSpec] at this
    have hz3 : h2.fromSpec z ∈ Set.range h12.fromSpec := by
      rw [h12.range_fromSpec]; exact ⟨hz1, hz2⟩
    obtain ⟨w, hw⟩ := hz3
    refine ⟨w, h2.fromSpec.isOpenEmbedding.injective ?_⟩
    rw [← hw, ← hb]
    rfl
  · rintro ⟨w, rfl⟩
    have : h12.fromSpec w ∈ W1 ⊓ W2 := by
      have h3 : h12.fromSpec w ∈ Set.range h12.fromSpec := ⟨w, rfl⟩
      rwa [h12.range_fromSpec] at h3
    have h4 : h2.fromSpec (Spec.map (Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op) w) ∈ W1 := by
      have h5 : h2.fromSpec (Spec.map (Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op) w) = h12.fromSpec w := by
        rw [← hb]; rfl
      rw [h5]; exact this.1
    change h2.fromSpec _ ∈ Set.range h1.fromSpec
    rw [h1.range_fromSpec]
    exact h4

private theorem germ_res' {Y : Scheme.{0}} [IsIntegral Y] {V W : Y.Opens} (h : V ≤ W) (hV : genericPoint Y ∈ V)
    (hW : genericPoint Y ∈ W) (f : Γ(Y, W)) :
    (Y.presheaf.germ V (genericPoint Y) hV).hom ((Y.presheaf.map (homOfLE h).op).hom f) =
      (Y.presheaf.germ W (genericPoint Y) hW).hom f :=
  congrArg (fun q => q.hom f) (TopCat.Presheaf.germ_res Y.presheaf (homOfLE h) (genericPoint Y) hV)

open scoped TensorProduct in
private theorem ringOn_inf {Y : Scheme.{0}} [IsIntegral Y] [Y.IsSeparated] (p' : Y ⟶ Sp ℂ)
    [instL : Algebra ℂ Y.functionField] (hL : instL = ffAlg p') {W1 W2 : Y.Opens} (h1 : IsAffineOpen W1)
    (h2 : IsAffineOpen W2) (g1 : genericPoint Y ∈ W1) (g2 : genericPoint Y ∈ W2) (g12 : genericPoint Y ∈ W1 ⊓ W2) :
    UpperTheory.A.ringOn p' hL W1 g1 ⊔ UpperTheory.A.ringOn p' hL W2 g2 = UpperTheory.A.ringOn p' hL (W1 ⊓ W2) g12 := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨f, rfl⟩
      exact ⟨(Y.presheaf.map (homOfLE (inf_le_left : W1 ⊓ W2 ≤ W1)).op).hom f, germ_res' _ g12 g1 f⟩
    · rintro _ ⟨f, rfl⟩
      exact ⟨(Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op).hom f, germ_res' _ g12 g2 f⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨t, rfl⟩ := surj_productMap h1.fromSpec h2.fromSpec _ _ (pb_aff h1 h2) g
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero]
      exact zero_mem _
    | add a b ha hb =>
      rw [map_add, map_add]
      exact add_mem ha hb
    | tmul a b =>
      rw [Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      refine mul_mem (Algebra.mem_sup_left ?_) (Algebra.mem_sup_right ?_)
      · exact ⟨a, (germ_res' _ g12 g1 a).symm⟩
      · exact ⟨b, (germ_res' _ g12 g2 b).symm⟩

private theorem mem_bot_of_int {F K : Type} [CommRing F] [Algebra ℂ F] [Field K] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] (T : Subalgebra ℂ F) (hT : T ≤ ⊥) {y : K} (hy : IsIntegral T y) : y ∈ (⊥ : Subalgebra ℂ K) := by
  haveI : Algebra.IsIntegral ℂ T := ⟨fun a => by
    obtain ⟨c, hc⟩ := Algebra.mem_bot.1 (hT a.2)
    have : a = algebraMap ℂ T c := Subtype.ext hc.symm
    rw [this]
    exact isIntegral_algebraMap⟩
  have h := isIntegral_trans (R := ℂ) (A := T) y hy
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible h)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one ℂ y hdeg
  exact Algebra.mem_bot.2 ⟨c, hc⟩

private theorem rA_empty_le {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → F) : rA ℂ x ∅ ≤ ⊥ := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨i, hi, -⟩
  simp at hi

private theorem rB_empty_le {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) : rB ℂ K x ∅ ≤ ⊥ :=
  fun _ hy => mem_bot_of_int (rA ℂ x ∅) (rA_empty_le x) hy

private theorem restriction_empty_le_bot {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K']
    [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K') : R2 x j2 ∅ ≤ ⊥ := by
  intro y hy
  refine mem_bot_of_int (F := K') ((rB ℂ K x ∅).map j2) ?_ hy
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 (rB_empty_le x hb)
  exact Algebra.mem_bot.2 ⟨c, (j2.commutes c).symm⟩

private theorem inf_join {Z Y : Scheme.{0}} {n : ℕ} (c1 c2 : Y ⟶ Z) (U : Fin n → Z.Opens) (S : Finset (Fin n ⊕ₗ Fin n)) :
    S.inf (UpperTheory.A.joinCover c1 c2 U) =
      (lft S).inf (fun i => c1 ⁻¹ᵁ U i) ⊓ (rgt S).inf (fun i => c2 ⁻¹ᵁ U i) := by
  classical
  have ml : ∀ i, i ∈ lft S ↔ toLex (Sum.inl i) ∈ S := fun i => by
    simp [lft, Finset.mem_toLeft]
  have mr : ∀ i, i ∈ rgt S ↔ toLex (Sum.inr i) ∈ S := fun i => by
    simp [rgt, Finset.mem_toRight]
  apply le_antisymm
  · refine le_inf (Finset.le_inf fun i hi => ?_) (Finset.le_inf fun i hi => ?_)
    · exact Finset.inf_le (f := UpperTheory.A.joinCover c1 c2 U) ((ml i).1 hi)
    · exact Finset.inf_le (f := UpperTheory.A.joinCover c1 c2 U) ((mr i).1 hi)
  · refine Finset.le_inf fun k hk => ?_
    rcases h : ofLex k with j | j
    · have hk' : k = toLex (Sum.inl j) := by rw [← h]; rfl
      subst hk'
      exact inf_le_left.trans (Finset.inf_le (f := fun i => c1 ⁻¹ᵁ U i) ((ml j).2 hk))
    · have hk' : k = toLex (Sum.inr j) := by rw [← h]; rfl
      subst hk'
      exact inf_le_right.trans (Finset.inf_le (f := fun i => c2 ⁻¹ᵁ U i) ((mr j).2 hk))

private theorem blocks_nonempty {n : ℕ} {S : Finset (Fin n ⊕ₗ Fin n)} (hS : S.Nonempty) :
    (lft S).Nonempty ∨ (rgt S).Nonempty := by
  obtain ⟨k, hk⟩ := hS
  rcases h : ofLex k with j | j
  · have hk' : k = toLex (Sum.inl j) := by rw [← h]; rfl
    subst hk'
    exact Or.inl ⟨j, by simpa [lft, Finset.mem_toLeft] using hk⟩
  · have hk' : k = toLex (Sum.inr j) := by rw [← h]; rfl
    subst hk'
    exact Or.inr ⟨j, by simpa [rgt, Finset.mem_toRight] using hk⟩

theorem UpperTheory.etaleCorrespondence_functionField_statement_two :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)), IsAffCover s' (UpperTheory.A.joinCover c1 c2 U) (fun S => RY x j2 (lft S) (rgt S)) := by

  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU
  have base := UpperTheory.A.isAffCover_join s s' c1 c2 hP hL U _ hU
  have C1 := (UpperTheory.A.isFinCover_pull h1 hK hL g1 hx hU).2
  have C2 := UpperTheory.etaleCorrespondence_functionField_statement_one d Z Y s s' hP c1 c2 h1 h2 hK hL g1 j2 g2 F x U hx hU
  haveI := UpperTheory.A.isSeparated_of_proj s hP
  haveI : Y.IsSeparated := UpperTheory.A.isSeparated_of_hom c1
  refine ⟨base.alg, base.affine, base.cover, base.ne, fun S hS y => ?_⟩
  have hcongr : ∀ {W W' : Y.Opens} (_ : W = W') (hW : genericPoint Y ∈ W) (hW' : genericPoint Y ∈ W'),
      UpperTheory.A.ringOn s' hL W hW = UpperTheory.A.ringOn s' hL W' hW' := by
    intro W W' e hW hW'
    subst e
    rfl
  have r1 : ∀ I : Finset (Fin (d + 1)), I.Nonempty →
      rB ℂ Y.functionField x I = UpperTheory.A.ringOn s' hL (I.inf fun i => c1 ⁻¹ᵁ U i) (C1.ne I) :=
    fun I hI => Subalgebra.ext (C1.ring I hI)
  have r2 : ∀ J : Finset (Fin (d + 1)), J.Nonempty →
      R2 x j2 J = UpperTheory.A.ringOn s' hL (J.inf fun i => c2 ⁻¹ᵁ U i) (C2.ne J) :=
    fun J hJ => Subalgebra.ext (C2.ring J hJ)
  have hinf := inf_join c1 c2 U S
  suffices h : RY x j2 (lft S) (rgt S) = UpperTheory.A.ringOn s' hL (S.inf (UpperTheory.A.joinCover c1 c2 U)) (base.ne S) by
    rw [h]
    exact Iff.rfl
  rcases (lft S).eq_empty_or_nonempty with hI | hI
  · have hJ : (rgt S).Nonempty := (blocks_nonempty hS).resolve_left (by simp [hI])
    have e : S.inf (UpperTheory.A.joinCover c1 c2 U) = (rgt S).inf fun i => c2 ⁻¹ᵁ U i := by
      rw [hinf, hI]
      simp
    rw [hcongr e _ (C2.ne _), ← r2 _ hJ, RY, hI]
    exact sup_eq_right.2 ((rB_empty_le x).trans bot_le)
  · rcases (rgt S).eq_empty_or_nonempty with hJ | hJ
    · have e : S.inf (UpperTheory.A.joinCover c1 c2 U) = (lft S).inf fun i => c1 ⁻¹ᵁ U i := by
        rw [hinf, hJ]
        simp
      rw [hcongr e _ (C1.ne _), ← r1 _ hI, RY, hJ]
      exact sup_eq_left.2 ((restriction_empty_le_bot x j2).trans bot_le)
    · rw [hcongr hinf _ (by rw [← hinf]; exact base.ne S), RY, r1 _ hI, r2 _ hJ]
      exact ringOn_inf s' hL (C1.affine _ hI) (C2.affine _ hJ) _ _ _
