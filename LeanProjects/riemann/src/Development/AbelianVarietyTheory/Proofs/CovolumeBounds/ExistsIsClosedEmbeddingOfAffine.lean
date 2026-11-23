import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

noncomputable section

namespace GlobalTheory.Points

open AlgebraicGeometry CategoryTheory Limits Topology Filter TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

section General

variable {C : Type} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C]
  {X S : Scheme.{0}}

theorem PtsOver.t2Space [T1Space C] (p : X ⟶ S) [IsSeparated p] (s : Sp C ⟶ S) : T2Space (PtsOver p s) := by
  rw [t2_iff_isClosed_diagonal]
  let h := PtsOver.prodHomeomorph (IsPullback.of_hasPullback p p) s
  have hd : pullback.diagonal p ≫ pullback.fst p p ≫ p = p := by simp
  have key : ∀ x, h (PtsOver.map (pullback.diagonal p) hd s x) = (x, x) := fun x =>
    Prod.ext (Subtype.ext (by simp [h])) (Subtype.ext (by simp [h]))
  have hc := (h.isClosedEmbedding.comp (PtsOver.isClosedEmbedding_map (pullback.diagonal p) hd s)).isClosed_range
  rw [show h ∘ PtsOver.map (pullback.diagonal p) hd s = fun x => (x, x) from funext key] at hc
  rwa [← Set.range_diag]

omit [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C] in

def PtsOver.baseChangeEquiv {P : Scheme.{0}} {g : P ⟶ X} {q : P ⟶ Sp C} {p : X ⟶ S} {s : Sp C ⟶ S}
    (hP : IsPullback g q p s) : Pts q ≃ PtsOver p s where
  toFun z := ⟨z.1 ≫ g, by rw [Category.assoc, hP.w, ← Category.assoc, z.2, Category.id_comp]⟩
  invFun x := ⟨hP.lift x.1 (𝟙 (Sp C)) (x.2.trans (Category.id_comp s).symm), hP.lift_snd _ _ _⟩
  left_inv z := Subtype.ext (hP.hom_ext (hP.lift_fst _ _ _) ((hP.lift_snd _ _ _).trans z.2.symm))
  right_inv x := Subtype.ext (hP.lift_fst _ _ _)

def PtsOver.baseChangeHomeomorph {P : Scheme.{0}} {g : P ⟶ X} {q : P ⟶ Sp C} {p : X ⟶ S} {s : Sp C ⟶ S}
    (hP : IsPullback g q p s) : Pts q ≃ₜ PtsOver p s where
  toEquiv := PtsOver.baseChangeEquiv hP
  continuous_toFun := ((continuous_comp g).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    refine continuous_induced_rng.2 ((isEmbedding_of_isPullback (C := C) hP).continuous_iff.2 ?_)
    have h : Continuous fun x : PtsOver p s => (x.1, 𝟙 (Sp C)) := continuous_subtype_val.prodMk continuous_const
    refine h.congr fun x => Prod.ext ?_ ?_
    · exact (congrArg Subtype.val ((PtsOver.baseChangeEquiv hP).apply_symm_apply x)).symm
    · exact ((PtsOver.baseChangeEquiv hP).symm x).2.symm

@[simp] theorem PtsOver.baseChangeHomeomorph_val {P : Scheme.{0}} {g : P ⟶ X} {q : P ⟶ Sp C} {p : X ⟶ S}
    {s : Sp C ⟶ S} (hP : IsPullback g q p s) (z : Pts q) :
    (PtsOver.baseChangeHomeomorph hP z).1 = z.1 ≫ g := rfl

theorem exists_isClosedEmbedding_of_affine [T1Space C] {A : CommRingCat.{0}} (q : Spec A ⟶ Sp C)
    [LocallyOfFiniteType q] : ∃ (n : ℕ) (c : Pts q → (Fin n → C)), IsClosedEmbedding c := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  have hφ : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 inferInstance
  letI := φ.hom.toAlgebra
  have : Algebra.FiniteType C A := hφ
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  refine ⟨n, _, isClosedEmbedding_coord (A := A) (id_eq_spMap_algebraMap C) (fun i => f (MvPolynomial.X i)) ?_⟩
  exact (congrArg (fun g : MvPolynomial (Fin n) C →ₐ[C] A => Function.Surjective g)
    (MvPolynomial.aeval_unique f)).mp hf

omit [IsTopologicalRing C] [IsOpenUnits C] [TopologicalSpace C] in

theorem mem_range_map_fromSpec (p : X ⟶ S) (s : Sp C ⟶ S) {U : X.Opens} (hU : IsAffineOpen U) (x : PtsOver p s)
    (hx : x.1 (IsLocalRing.closedPoint C) ∈ U) :
    x ∈ Set.range (PtsOver.map (p := hU.fromSpec ≫ p) hU.fromSpec rfl s) := by
  rw [PtsOver.range_map, range_comp_of_isOpenImmersion, IsAffineOpen.opensRange_fromSpec]
  exact (le_preimage_iff x.1 U).2 hx

theorem Pts.locallyCompactSpace [T1Space C] [LocallyCompactSpace C] (p : X ⟶ Sp C) [LocallyOfFiniteType p] :
    LocallyCompactSpace (Pts p) := by
  refine ⟨fun x n hn => ?_⟩
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_le x.1 (le_preimage_top _)
  obtain ⟨y, rfl⟩ := mem_range_map_fromSpec p _ hU x ((le_preimage_iff _ _).1 hx)
  obtain ⟨m, c, hc⟩ := exists_isClosedEmbedding_of_affine (hU.fromSpec ≫ p)
  have := hc.locallyCompactSpace
  have he := PtsOver.isOpenEmbedding_map (p := hU.fromSpec ≫ p) hU.fromSpec rfl (𝟙 (Sp C))
  obtain ⟨K, hK, hKn, hKc⟩ := local_compact_nhds (he.continuous.continuousAt.preimage_mem_nhds hn)
  exact ⟨_, he.isOpenMap.image_mem_nhds hK, Set.image_subset_iff.2 hKn, hKc.image he.continuous⟩

theorem PtsOver.locallyCompactSpace [T1Space C] [LocallyCompactSpace C] (p : X ⟶ S) [LocallyOfFiniteType p]
    (s : Sp C ⟶ S) : LocallyCompactSpace (PtsOver p s) :=
  have := Pts.locallyCompactSpace (pullback.snd p s)
  (PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback p s)).symm.isClosedEmbedding.locallyCompactSpace

theorem Pts.secondCountableTopology_of_cover [T1Space C] [SecondCountableTopology C] (p : X ⟶ Sp C)
    [LocallyOfFiniteType p] {ι : Type*} [Countable ι] {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i))
    (hc : iSup U = ⊤) : SecondCountableTopology (Pts p) := by
  have he := fun i => PtsOver.isOpenEmbedding_map (p := (hU i).fromSpec ≫ p) (hU i).fromSpec rfl (𝟙 (Sp C))
  have : ∀ i, SecondCountableTopology
      (Set.range (PtsOver.map (p := (hU i).fromSpec ≫ p) (hU i).fromSpec rfl (𝟙 (Sp C)))) := fun i => by
    obtain ⟨m, c, hc⟩ := exists_isClosedEmbedding_of_affine ((hU i).fromSpec ≫ p)
    have := hc.isEmbedding.secondCountableTopology
    exact (he i).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine secondCountableTopology_of_countable_cover (fun i => (he i).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top x.1 hc
  exact Set.mem_iUnion.2 ⟨i, mem_range_map_fromSpec p _ (hU i) x ((le_preimage_iff _ _).1 hi)⟩

theorem PtsOver.secondCountableTopology [T1Space C] [SecondCountableTopology C] (p : X ⟶ S)
    [LocallyOfFiniteType p] [QuasiCompact p] (s : Sp C ⟶ S) : SecondCountableTopology (PtsOver p s) := by
  have : CompactSpace (pullback p s : Scheme.{0}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p s)
  let 𝒰 := (pullback p s).affineCover.finiteSubcover
  have := Pts.secondCountableTopology_of_cover (pullback.snd p s)
    (U := fun i => (𝒰.f i).opensRange) (fun i => isAffineOpen_opensRange _) 𝒰.iSup_opensRange
  exact (PtsOver.baseChangeHomeomorph (IsPullback.of_hasPullback p s)).symm.secondCountableTopology

open scoped MonObj in

theorem continuousMul_over (A : Over (Sp C)) [MonObj A] : ContinuousMul (𝟙_ (Over (Sp C)) ⟶ A) where
  continuous_mul := (continuous_over_comp (μ[A])).comp (tensorHomeomorph A A).symm.continuous

open scoped MonObj in

theorem isTopologicalGroup_over (A : Over (Sp C)) [GrpObj A] : IsTopologicalGroup (𝟙_ (Over (Sp C)) ⟶ A) where
  continuous_mul := (continuousMul_over A).continuous_mul
  continuous_inv := continuous_over_comp (GrpObj.inv (X := A))

variable {R : Type} [CommRing R] {N : ℕ}

omit [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C] in

theorem le_pt_preimage_chart_iff (c : R →+* C) (v : Fin (N + 1) → C) (hv : Ideal.span (Set.range v) = ⊤)
    (i : Fin (N + 1)) : ⊤ ≤ pt c v hv ⁻¹ᵁ chart R N i ↔ IsUnit (v i) := by
  rw [pt_preimage_chart, top_le_iff]
  rw [← Ideal.span_singleton_eq_top, ← Set.range_const (ι := Unit), ← iSup_spOpen_eq_top_iff, iSup_const]

omit [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C] in

theorem valR_pt_ratio (c : R →+* C) (v : Fin (N + 1) → C) (hv : Ideal.span (Set.range v) = ⊤)
    {i : Fin (N + 1)} (hi : IsUnit (v i)) (j : Fin (N + 1)) :
    valR (pt c v hv) (chart R N i) (ratio R N i j) = v j * Ring.inverse (v i) := by
  have h := (le_pt_preimage_chart_iff c v hv i).2 hi
  have e : ∀ a : C, (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (fnOn ⊤ a) = a := fun a =>
    (congrArg _ (GlobalTheory.Cartier.resG_self (X := Sp C) le_top _)).trans (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of C)) a)
  have h1 := congrArg (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (pullRatio_pt_top_mul c v hv i j hi h)
  rw [map_mul, e, e] at h1
  rw [valR_eq _ _ h, ← h1, mul_assoc, Ring.mul_inverse_cancel _ hi, mul_one]
  rfl

def projPt (c : R →+* C) (v : Unimodular C N) : PtsOver (PSpace.str R N) (spMap c) :=
  ⟨pt c v.1 v.2, pt_str c v.1 v.2⟩

omit [TopologicalSpace C] [IsTopologicalRing C] [IsOpenUnits C] in

theorem projPt_surjective (c : R →+* C) : Function.Surjective (projPt (N := N) c) := fun x =>
  (exists_eq_pt c x.1 x.2).elim fun v h => h.elim fun hv e => ⟨⟨v, hv⟩, Subtype.ext e.symm⟩

omit [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C] in

theorem projPt_eq_iff (c : R →+* C) (v w : Unimodular C N) :
    projPt c v = projPt c w ↔ ∃ u : Cˣ, w.1 = u • v.1 :=
  Subtype.ext_iff.trans (pt_eq_pt_iff c v.2 w.2)

theorem continuous_projPt (c : R →+* C) : Continuous (projPt (N := N) c) := by
  have hs : ∀ i, Subring.closure (Set.range (constFn (PSpace.str R N) (chart R N i)) ∪
      Set.range (ratio R N i)) = ⊤ := fun i => by
    have := (Algebra.adjoin_range_eq_range_aeval R (ratio R N i)).trans
      ((AlgHom.range_eq_top _).2 (aeval_ratio_surjective R N i))
    have h2 := congrArg Subalgebra.toSubring this
    rw [Algebra.adjoin_eq_ring_closure] at h2
    exact h2
  refine (PtsOver.continuous_iff_of_generators (isAffineOpen_chart R N) (iSup_chart R N) hs).2 fun i => ?_
  have hset : {b : Unimodular C N | ⊤ ≤ (projPt c b).1 ⁻¹ᵁ chart R N i} = {b | IsUnit (b.1 i)} :=
    Set.ext fun b => le_pt_preimage_chart_iff c b.1 b.2 i
  have hcont : ∀ j, Continuous fun b : Unimodular C N => b.1 j := fun j =>
    (continuous_apply j).comp continuous_subtype_val
  rw [hset]
  refine ⟨(IsOpenUnits.isOpenEmbedding_unitsVal (M := C)).isOpen_range.preimage (hcont i), ?_⟩
  rintro _ ⟨j, rfl⟩
  refine ContinuousOn.congr (fun b hb => ?_) fun b hb => valR_pt_ratio c b.1 b.2 hb j
  exact ((hcont j).continuousAt.mul
    (ContinuousAt.comp (f := fun b : Unimodular C N => b.1 i) (continuousAt_inverse_of_isUnit hb)
      (hcont i).continuousAt)).continuousWithinAt

end General

section Normed

variable {F : Type} [NormedField F] {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}}

def supSpherePt (c : R →+* F) (N : ℕ) (v : Metric.sphere (0 : Fin (N + 1) → F) 1) :
    PtsOver (PSpace.str R N) (spMap c) :=
  projPt c ⟨v.1, span_range_eq_top_iff_ne_zero.2 (ne_zero_of_mem_unit_sphere v)⟩

theorem continuous_supSpherePt (c : R →+* F) : Continuous (supSpherePt c N) :=
  (continuous_projPt c).comp (continuous_subtype_val.subtype_mk _)

theorem supSpherePt_surjective (c : R →+* F) : Function.Surjective (supSpherePt c N) := by
  intro x
  obtain ⟨⟨v, hv⟩, rfl⟩ := projPt_surjective c x
  have h0 : v ≠ 0 := span_range_eq_top_iff_ne_zero.1 hv
  obtain ⟨i, hi⟩ := Finite.exists_max fun j => ‖v j‖
  have hn : ‖v‖ = ‖v i‖ := le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hi) (norm_le_pi_norm v i)
  have hvi : v i ≠ 0 := fun h => h0 (by rwa [h, norm_zero, norm_eq_zero] at hn)
  refine ⟨⟨(v i)⁻¹ • v, ?_⟩, Subtype.ext (pt_units_smul c hv (Units.mk0 _ hvi)⁻¹)⟩
  rw [mem_sphere_zero_iff_norm, norm_smul, hn, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.2 hvi)]

theorem compactSpace_pSpace [ProperSpace F] (c : R →+* F) (N : ℕ) :
    CompactSpace (PtsOver (PSpace.str R N) (spMap c)) :=
  (supSpherePt_surjective c).compactSpace (continuous_supSpherePt c)

theorem PtsOver.compactSpace [ProperSpace F] {p : X ⟶ Sp R} (hp : IsProjOver p) (s : Sp F ⟶ Sp R) :
    CompactSpace (PtsOver p s) := by
  obtain ⟨c, rfl⟩ := Spec.map_surjective s
  obtain ⟨N, i, _, hi⟩ := hp
  have := compactSpace_pSpace c.hom N
  exact (PtsOver.isClosedEmbedding_map i hi (spMap c.hom)).compactSpace

end Normed

section Sphere

variable {𝕜 : Type} [RCLike 𝕜] {R : Type} [CommRing R] {N : ℕ}

theorem span_range_sphere (v : Metric.sphere (0 : EuclideanSpace 𝕜 (Fin (N + 1))) 1) :
    Ideal.span (Set.range v.1.ofLp) = ⊤ :=
  span_range_eq_top_iff_ne_zero.2 fun h => ne_zero_of_mem_unit_sphere v ((WithLp.ofLp_eq_zero 2).1 h)

def spherePt (c : R →+* 𝕜) (N : ℕ) (v : Metric.sphere (0 : EuclideanSpace 𝕜 (Fin (N + 1))) 1) :
    PtsOver (PSpace.str R N) (spMap c) :=
  projPt c ⟨v.1.ofLp, span_range_sphere v⟩

theorem continuous_spherePt (c : R →+* 𝕜) : Continuous (spherePt c N) :=
  (continuous_projPt c).comp (((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val).subtype_mk _)

theorem spherePt_surjective (c : R →+* 𝕜) : Function.Surjective (spherePt c N) := by
  intro x
  obtain ⟨⟨v, hv⟩, rfl⟩ := projPt_surjective c x
  have h0 : WithLp.toLp 2 v ≠ 0 := fun h => span_range_eq_top_iff_ne_zero.1 hv ((WithLp.toLp_eq_zero 2).1 h)
  have hn : ((‖WithLp.toLp 2 v‖ : ℝ) : 𝕜) ≠ 0 := by simpa using h0
  refine ⟨⟨((‖WithLp.toLp 2 v‖ : ℝ) : 𝕜)⁻¹ • WithLp.toLp 2 v, ?_⟩,
    Subtype.ext (pt_units_smul c hv (Units.mk0 _ hn)⁻¹)⟩
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]

end Sphere

open scoped MonObj in

theorem complex_points_topology :
    (∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ),
      (IsSeparated p → T2Space (Pts p)) ∧
      (LocallyOfFiniteType p → LocallyCompactSpace (Pts p)) ∧
      (LocallyOfFiniteType p → QuasiCompact p → SecondCountableTopology (Pts p)) ∧
      (IsProjOver p → CompactSpace (Pts p))) ∧
    (∀ N : ℕ, ∃ π : Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1 → Pts (PSpace.str ℂ N),
      (∀ v, (π v).1 = pt (RingHom.id ℂ) v.1.ofLp (span_range_sphere v)) ∧ Continuous π ∧ Function.Surjective π) ∧
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsTopologicalGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) := by
  refine ⟨fun X p => ⟨fun _ => PtsOver.t2Space p _, fun _ => PtsOver.locallyCompactSpace p _,
    fun _ _ => PtsOver.secondCountableTopology p _, fun h => PtsOver.compactSpace h _⟩, fun N => ?_,
    fun A _ => isTopologicalGroup_over A⟩
  unfold Pts
  rw [id_eq_spMap_algebraMap ℂ]
  exact ⟨spherePt (RingHom.id ℂ) N, fun _ => rfl, continuous_spherePt _, spherePt_surjective _⟩

example : let P := PtsOver (PSpace.str ℂ 1) (spMap (RingHom.id ℂ))
    CompactSpace P ∧ Nontrivial P := by
  refine ⟨compactSpace_pSpace _ 1, projPt _ ⟨![1, 0], span_range_eq_top_iff_ne_zero.2 (by simp)⟩,
    projPt _ ⟨![0, 1], span_range_eq_top_iff_ne_zero.2 (by simp)⟩, fun h => ?_⟩
  obtain ⟨u, hu⟩ := (projPt_eq_iff _ _ _).1 h
  simpa using congrFun hu 1

end GlobalTheory.Points
