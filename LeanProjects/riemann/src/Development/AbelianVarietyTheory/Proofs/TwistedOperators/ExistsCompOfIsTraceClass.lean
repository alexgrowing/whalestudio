import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TraceKernelDecomposition
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableDescendOrbitSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLocallyFiniteContinuous

noncomputable section

open MeasureTheory ContinuousLinearMap Filter GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.TraceKernelDecomposition
open scoped InnerProductSpace Topology ComplexConjugate

namespace GlobalTheory.TraceDiagonal

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma norm_toL1_inner_le_mul_norm {X : Type*} [MeasurableSpace X] {ν : Measure X} (f g : Lp ℂ 2 ν) :
    ‖(L2.integrable_inner f g).toL1 (fun x => ⟪f x, g x⟫_ℂ)‖ ≤ ‖f‖ * ‖g‖ := by
  have : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 2) (q := 2) (r := 1) (μ := ν)
    (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable g) (fun u v : ℂ => ⟪u, v⟫_ℂ) 1
    (Filter.Eventually.of_forall fun x => by simpa using norm_inner_le_norm (𝕜 := ℂ) (f x) (g x))
  have e : ‖(L2.integrable_inner f g).toL1 (fun x => ⟪f x, g x⟫_ℂ)‖
      = (eLpNorm (fun x => ⟪f x, g x⟫_ℂ) 1 ν).toReal := by
    simp [Integrable.toL1, Lp.norm_toLp]
  rw [e, Lp.norm_def f, Lp.norm_def g, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)) ?_
  simpa using h

theorem exists_comp_of_isTraceClass {T : H →L[ℂ] H} (h : IsTraceClass T) :
    ∃ B C : H →L[ℂ] H, IsHilbertSchmidt B ∧ IsHilbertSchmidt C ∧ T = B ∘L C := by
  set e := stdBasis H
  have hsum := (isTraceClass_iff_abs e).1 h
  have hA0 : 0 ≤ CFC.abs T := CFC.abs_nonneg T
  set A := CFC.abs T with hA
  set S := CFC.sqrt A with hS
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA0
  have hSsa : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hAeq : A = CFC.sqrt (adjoint T ∘L T) := by
    simp only [hA, CFC.abs, ContinuousLinearMap.star_eq_adjoint]; rfl
  have hnorm : ∀ x, ‖T x‖ ≤ ‖A x‖ := by
    intro x
    rw [hAeq, norm_sqrt_apply]
  obtain ⟨U, hU⟩ := exists_comp_eq_of_norm_le hnorm
  have hSx : ∀ x, ‖S x‖ ^ 2 = RCLike.re ⟪x, A x⟫_ℂ := by
    intro x
    rw [← hSS]
    change ‖S x‖ ^ 2 = RCLike.re ⟪x, S (S x)⟫_ℂ
    rw [← @inner_self_eq_norm_sq ℂ, ← adjoint_inner_right, hSsa.adjoint_eq]
  have hSHS : IsHilbertSchmidt S := by
    rw [isHilbertSchmidt_iff e]
    refine (hsum.mapL Complex.reCLM).congr (fun i => ?_)
    rw [hSx]; rfl
  refine ⟨U ∘L S, S, hSHS.comp_left U, hSHS, ?_⟩
  rw [← hU, ← hSS]; rfl

theorem exists_rankOne_expansion {T : H →L[ℂ] H} (h : IsTraceClass T) :
    ∃ a b : stdIndex H → H, Summable (fun j => ‖b j‖ * ‖a j‖) ∧
      (∀ ψ φ, HasSum (fun j => ⟪ψ, a j⟫_ℂ * ⟪b j, φ⟫_ℂ) ⟪ψ, T φ⟫_ℂ) ∧
      HasSum (fun j => ⟪b j, a j⟫_ℂ) (trace T) := by
  obtain ⟨B, C, hB, hC, rfl⟩ := exists_comp_of_isTraceClass h
  set e := stdBasis H
  have hB2 : Summable fun j => ‖B (e j)‖ ^ 2 := (isHilbertSchmidt_iff e).1 hB
  have hC2 : Summable fun j => ‖adjoint C (e j)‖ ^ 2 := (isHilbertSchmidt_iff e).1 hC.adjoint
  refine ⟨fun j => B (e j), fun j => adjoint C (e j), ?_, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) (hC2.add hB2)
    nlinarith [sq_nonneg (‖adjoint C (e j)‖ - ‖B (e j)‖), norm_nonneg (adjoint C (e j)),
      norm_nonneg (B (e j))]
  · intro ψ φ
    have h1 := e.hasSum_inner_mul_inner (adjoint B ψ) (C φ)
    have h2 : ⟪ψ, (B ∘L C) φ⟫_ℂ = ⟪adjoint B ψ, C φ⟫_ℂ := by rw [adjoint_inner_left]; rfl
    have h3 : (fun j => ⟪ψ, B (e j)⟫_ℂ * ⟪adjoint C (e j), φ⟫_ℂ) =
        fun i => ⟪adjoint B ψ, e i⟫_ℂ * ⟪e i, C φ⟫_ℂ := by
      funext j; rw [adjoint_inner_left, adjoint_inner_left]
    show HasSum (fun j => ⟪ψ, B (e j)⟫_ℂ * ⟪adjoint C (e j), φ⟫_ℂ) _
    rw [h3, h2]; exact h1
  · have h1 := hasSum_trace_comp e hC hB
    rw [← trace_comp_comm hB hC] at h1
    have h3 : (fun j => ⟪adjoint C (e j), B (e j)⟫_ℂ) = fun i => ⟪e i, (C ∘L B) (e i)⟫_ℂ := by
      funext j; rw [adjoint_inner_left]; rfl
    show HasSum (fun j => ⟪adjoint C (e j), B (e j)⟫_ℂ) _
    rw [h3]; exact h1

def projSum {n : ℕ} (v : Fin n → H) (c : Fin n → ℝ) : H →L[ℂ] H :=
  ∑ i, ((c i : ℂ)⁻¹) • InnerProductSpace.rankOne ℂ (v i) (v i)

omit [CompleteSpace H] in

theorem inner_projSum {n : ℕ} (v : Fin n → H) (c : Fin n → ℝ) (b a : H) :
    ⟪b, projSum v c a⟫_ℂ = ∑ i, (c i : ℂ)⁻¹ * (⟪v i, a⟫_ℂ * ⟪b, v i⟫_ℂ) := by
  simp [projSum, InnerProductSpace.rankOne_apply]

theorem norm_projSum_le {n : ℕ} {v : Fin n → H} {c : Fin n → ℝ} (h : ∀ i, ⟪v i, v i⟫_ℂ = c i)
    (h' : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℂ = 0) : ‖projSum v c‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => ?_
  rw [one_mul]
  have hv : ∀ i, ⟪v i, projSum v c a⟫_ℂ = ((c i : ℂ)⁻¹ * (c i : ℂ)) * ⟪v i, a⟫_ℂ := by
    intro i
    rw [inner_projSum, Finset.sum_eq_single i]
    · rw [h i]; ring
    · intro j _ hji
      rw [h' i j (Ne.symm hji)]
      ring
    · simp
  have hPP : ⟪projSum v c a, projSum v c a⟫_ℂ = ⟪a, projSum v c a⟫_ℂ := by
    rw [inner_projSum v c (projSum v c a) a, inner_projSum v c a a]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← inner_conj_symm (projSum v c a) (v i), hv i, ← inner_conj_symm a (v i)]
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    by_cases hc : (c i : ℂ) = 0
    · simp [hc]
    · rw [inv_mul_cancel₀ hc, one_mul]
  have h0 : ⟪a - projSum v c a, projSum v c a⟫_ℂ = 0 := by
    rw [inner_sub_left, hPP, sub_self]
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a - projSum v c a) (projSum v c a) h0
  rw [sub_add_cancel] at hn
  have hle : ‖projSum v c a‖ * ‖projSum v c a‖ ≤ ‖a‖ * ‖a‖ := by
    rw [hn]
    nlinarith [mul_self_nonneg ‖a - projSum v c a‖]
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 hle

omit [CompleteSpace H] in

theorem tendsto_inner_of_dense {P : ℕ → (H →L[ℂ] H)} (hP : ∀ m, ‖P m‖ ≤ 1) {S : Set H} (hS : Dense S)
    {q : H → H → ℂ} (hq : Continuous (Function.uncurry q))
    (h : ∀ b ∈ S, ∀ a ∈ S, Tendsto (fun m => ⟪b, P m a⟫_ℂ) atTop (𝓝 (q b a))) (b a : H) :
    Tendsto (fun m => ⟪b, P m a⟫_ℂ) atTop (𝓝 (q b a)) := by
  have hb : ∀ m (y : H), ‖P m y‖ ≤ ‖y‖ := fun m y =>
    ((P m).le_of_opNorm_le (hP m) y).trans_eq (one_mul _)
  have hlip1 : ∀ a' : H, UniformEquicontinuous (fun m (x : H) => ⟪x, P m a'⟫_ℂ) := by
    intro a'
    refine LipschitzWith.uniformEquicontinuous _ ‖a'‖₊ fun m => LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, ← inner_sub_left]
    calc ‖⟪x - y, P m a'⟫_ℂ‖ ≤ ‖x - y‖ * ‖P m a'‖ := norm_inner_le_norm _ _
      _ ≤ ‖x - y‖ * ‖a'‖ := by gcongr; exact hb m a'
      _ = ‖a'‖₊ * ‖x - y‖ := by rw [coe_nnnorm, mul_comm]
  have hlip2 : ∀ b' : H, UniformEquicontinuous (fun m (y : H) => ⟪b', P m y⟫_ℂ) := by
    intro b'
    refine LipschitzWith.uniformEquicontinuous _ ‖b'‖₊ fun m => LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, ← inner_sub_right, ← map_sub]
    calc ‖⟪b', P m (x - y)⟫_ℂ‖ ≤ ‖b'‖ * ‖P m (x - y)‖ := norm_inner_le_norm _ _
      _ ≤ ‖b'‖ * ‖x - y‖ := by gcongr; exact hb m _
      _ = ‖b'‖₊ * ‖x - y‖ := by rw [coe_nnnorm]
  have step1 : ∀ a' ∈ S, ∀ b' : H, Tendsto (fun m => ⟪b', P m a'⟫_ℂ) atTop (𝓝 (q b' a')) := by
    intro a' ha' b'
    have hf : Continuous fun x => q x a' := hq.comp (Continuous.prodMk_left a')
    have hcl := (hlip1 a').equicontinuous.isClosed_setOfPred_tendsto (l := atTop) hf
    exact hcl.closure_subset_iff.2 (fun x hx => h x hx a' ha') (hS b')
  have hf : Continuous fun y => q b y := hq.comp (Continuous.prodMk_right b)
  have hcl := (hlip2 b).equicontinuous.isClosed_setOfPred_tendsto (l := atTop) hf
  exact hcl.closure_subset_iff.2 (fun y hy => step1 y hy b) (hS a)

end Hilbert

section Measure

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

theorem exists_diagonal {ι : Type*} {a b : ι → Lp ℂ 2 ν} (h : Summable fun j => ‖b j‖ * ‖a j‖) :
    ∃ d : X → ℂ, Integrable d ν ∧ ∀ E, HasSum (fun j => ∫ x in E, ⟪b j x, a j x⟫_ℂ ∂ν) (∫ x in E, d x ∂ν) := by
  have hI : ∀ j, Integrable (fun x => ⟪b j x, a j x⟫_ℂ) ν := fun j => L2.integrable_inner (b j) (a j)
  have hs : Summable fun j => (hI j).toL1 (fun x => ⟪b j x, a j x⟫_ℂ) :=
    Summable.of_norm_bounded h (fun j => norm_toL1_inner_le_mul_norm (b j) (a j))
  refine ⟨⇑(∑' j, (hI j).toL1 (fun x => ⟪b j x, a j x⟫_ℂ)), L1.integrable_coeFn _, fun E => ?_⟩
  let g : (X →₁[ν] ℂ) →+ ℂ :=
    { toFun := fun f => ∫ x in E, f x ∂ν
      map_zero' := by
        rw [integral_congr_ae (Lp.coeFn_zero ℂ 1 ν).restrict]
        simp
      map_add' := fun f f' => by
        rw [integral_congr_ae (Lp.coeFn_add f f').restrict]
        exact integral_add (L1.integrable_coeFn f).integrableOn (L1.integrable_coeFn f').integrableOn }
  have hg : Continuous g := continuous_setIntegral E
  have := hs.hasSum.map g hg
  convert this using 1
  · funext j
    simp only [Function.comp_apply, g, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact integral_congr_ae ((Integrable.coeFn_toL1 (hI j)).restrict).symm
  · rfl

variable [IsFiniteMeasure ν]

theorem norm_mean_sub_le {F : X → X → ℂ} (hF : StronglyMeasurable (Function.uncurry F)) {A : Set X}
    (hA : MeasurableSet A) {M ε : ℝ} (hM : ∀ x ∈ A, ∀ y ∈ A, ‖F x y‖ ≤ M)
    (hε : ∀ x ∈ A, ∀ y ∈ A, ‖F x y - F x x‖ ≤ ε) :
    ‖(ν.real A : ℂ)⁻¹ * ∫ x in A, ∫ y in A, F x y ∂ν ∂ν - ∫ x in A, F x x ∂ν‖ ≤ ε * ν.real A := by
  have hfin : ν A < ⊤ := measure_lt_top ν A
  have hsec : ∀ x, StronglyMeasurable (fun y => F x y) := fun x =>
    hF.comp_measurable measurable_prodMk_left
  have hdiagm : StronglyMeasurable (fun x => F x x) :=
    hF.comp_measurable (measurable_id.prodMk measurable_id)
  have hgm : StronglyMeasurable (fun x => ∫ y in A, F x y ∂ν) :=
    StronglyMeasurable.integral_prod_right (f := F) hF
  rcases (measureReal_nonneg : 0 ≤ ν.real A).eq_or_lt with h0 | hpos
  · have hA0 : ν A = 0 := (measureReal_eq_zero_iff).1 h0.symm
    have hr : ν.restrict A = 0 := Measure.restrict_eq_zero.mpr hA0
    simp [hr, ← h0]
  · have hsecI : ∀ x ∈ A, IntegrableOn (fun y => F x y) A ν := fun x hx =>
      Measure.integrableOn_of_bounded hfin.ne (hsec x).aestronglyMeasurable (M := M)
        ((ae_restrict_iff' hA).2 (Filter.Eventually.of_forall fun y hy => hM x hx y hy))
    have hdiagI : IntegrableOn (fun x => F x x) A ν :=
      Measure.integrableOn_of_bounded hfin.ne hdiagm.aestronglyMeasurable (M := M)
        ((ae_restrict_iff' hA).2 (Filter.Eventually.of_forall fun x hx => hM x hx x hx))
    have hgI : IntegrableOn (fun x => ∫ y in A, F x y ∂ν) A ν :=
      Measure.integrableOn_of_bounded hfin.ne hgm.aestronglyMeasurable (M := M * ν.real A)
        ((ae_restrict_iff' hA).2 (Filter.Eventually.of_forall fun x hx =>
          norm_setIntegral_le_of_norm_le_const hfin (fun y hy => hM x hx y hy)))
    have hc0 : ((ν.real A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have e1 : ((ν.real A : ℝ) : ℂ)⁻¹ * ∫ x in A, ∫ y in A, F x y ∂ν ∂ν
        = ∫ x in A, ((ν.real A : ℝ) : ℂ)⁻¹ * ∫ y in A, F x y ∂ν ∂ν := (integral_const_mul _ _).symm
    have key : ((ν.real A : ℝ) : ℂ)⁻¹ * ∫ x in A, ∫ y in A, F x y ∂ν ∂ν - ∫ x in A, F x x ∂ν
        = ∫ x in A, ((ν.real A : ℝ) : ℂ)⁻¹ * ∫ y in A, (F x y - F x x) ∂ν ∂ν := by
      rw [e1, ← integral_sub (hgI.const_mul _) hdiagI]
      refine setIntegral_congr_fun hA (fun x hx => ?_)
      rw [integral_sub (hsecI x hx) (integrableOn_const hfin.ne), setIntegral_const,
        Complex.real_smul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    rw [key]
    have hb : ∀ x ∈ A, ‖((ν.real A : ℝ) : ℂ)⁻¹ * ∫ y in A, (F x y - F x x) ∂ν‖ ≤ ε := by
      intro x hx
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le, inv_mul_le_iff₀ hpos]
      have := norm_setIntegral_le_of_norm_le_const hfin (fun y hy => hε x hx y hy)
      linarith [mul_comm ε (ν.real A)]
    exact norm_setIntegral_le_of_norm_le_const hfin hb

variable {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] {s : X → Y}

omit [IsFiniteMeasure ν] in

theorem exists_partition (hs : Measurable s) {Ω : Set Y} (hΩ : IsCompact Ω) {E : Set X} (hE : MeasurableSet E)
    (hEΩ : E ⊆ s ⁻¹' Ω) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (A : Fin n → Set X), (∀ i, MeasurableSet (A i)) ∧ Pairwise (Function.onFun Disjoint A) ∧
      ⋃ i, A i = E ∧ ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist (s x) (s y) < δ := by
  obtain ⟨t, -, ht⟩ := hΩ.elim_nhds_subcover (fun y => Metric.ball y (δ / 2))
    (fun y _ => Metric.ball_mem_nhds y (half_pos hδ))
  let L := t.toList
  let B : Fin L.length → Set X := fun i => E ∩ s ⁻¹' Metric.ball (L.get i) (δ / 2)
  have hB : ∀ i, MeasurableSet (B i) := fun i => hE.inter (hs Metric.isOpen_ball.measurableSet)
  refine ⟨L.length, fun i => B i \ ⋃ j ∈ Set.Iio i, B j, fun i => ?_, ?_, ?_, ?_⟩
  · exact (hB i).diff (MeasurableSet.biUnion (Set.to_countable _) fun j _ => hB j)
  · intro i j hij
    simp only [Function.onFun]
    rcases lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_left.2 fun x hx hy => hy.2 (Set.mem_biUnion (Set.mem_Iio.2 h) hx.1)
    · exact Set.disjoint_left.2 fun x hx hy => hx.2 (Set.mem_biUnion (Set.mem_Iio.2 h) hy.1)
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i x hx => hx.1.1
    · intro x hx
      have hx' : ∃ i, x ∈ B i := by
        obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (ht (hEΩ hx))
        obtain ⟨i, hi⟩ := List.mem_iff_get.1 (Finset.mem_toList.2 hyt)
        refine ⟨i, hx, ?_⟩
        show s x ∈ Metric.ball (L.get i) (δ / 2)
        rw [hi]
        exact hy
      obtain ⟨i, hi⟩ := hx'
      let S : Set (Fin L.length) := {i | x ∈ B i}
      have hne : S.Nonempty := ⟨i, hi⟩
      refine Set.mem_iUnion.2 ⟨wellFounded_lt.min S hne, wellFounded_lt.min_mem S hne, ?_⟩
      simp only [Set.mem_iUnion]
      rintro ⟨j, hj, hxj⟩
      exact wellFounded_lt.not_lt_min S hxj hj
  · intro i x hx y hy
    have h1 : s x ∈ Metric.ball (L.get i) (δ / 2) := hx.1.2
    have h2 : s y ∈ Metric.ball (L.get i) (δ / 2) := hy.1.2
    rw [Metric.mem_ball] at h1 h2
    calc dist (s x) (s y) ≤ dist (s x) (L.get i) + dist (s y) (L.get i) := dist_triangle_right _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add h1 h2
      _ = δ := by ring

theorem dense_continuous (hs : MeasurableEmbedding s) :
    Dense {a : Lp ℂ 2 ν | ∃ g : Y → ℂ, Continuous g ∧ a =ᵐ[ν] fun x => g (s x)} := by
  intro a
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε => ?_
  have hFs : Function.extend s (a : X → ℂ) 0 ∘ s = (a : X → ℂ) := Function.extend_comp hs.injective _ _
  have hF : MemLp (Function.extend s (a : X → ℂ) 0) 2 (ν.map s) := by
    rw [hs.memLp_map_measure_iff, hFs]
    exact Lp.memLp a
  obtain ⟨g, hg, g_mem⟩ := hF.exists_boundedContinuous_eLpNorm_sub_le ENNReal.ofNat_ne_top hε.ne'
  have g_mem' : MemLp (fun x => g (s x)) 2 ν := (hs.memLp_map_measure_iff).1 g_mem
  refine ⟨g_mem'.toLp _, ⟨g, g.continuous, MemLp.coeFn_toLp g_mem'⟩, ?_⟩
  rw [Metric.mem_closedEBall', ← Lp.toLp_coeFn a (Lp.memLp a), Lp.edist_toLp_toLp]
  rw [hs.eLpNorm_map_measure] at hg
  convert hg using 2
  funext x
  have h1 := congr_fun hFs x
  simp only [Function.comp_apply] at h1
  simp [h1]

variable [SecondCountableTopology Y]

theorem exists_partitions (hs : Measurable s) {Ω : Set Y} (hΩ : IsCompact Ω) {E : Set X} (hE : MeasurableSet E)
    (hEΩ : E ⊆ s ⁻¹' Ω) :
    ∃ (n : ℕ → ℕ) (A : ∀ m, Fin (n m) → Set X), (∀ m i, MeasurableSet (A m i)) ∧
      (∀ m, Pairwise (Function.onFun Disjoint (A m))) ∧ ∀ k : Y × Y → ℂ, Continuous k →
        Tendsto (fun m => ∑ i, (ν.real (A m i) : ℂ)⁻¹ * ∫ x in A m i, ∫ y in A m i, k (s x, s y) ∂ν ∂ν) atTop
          (𝓝 (∫ x in E, k (s x, s x) ∂ν)) := by
  have hP : ∀ m : ℕ, ∃ (n : ℕ) (A : Fin n → Set X), (∀ i, MeasurableSet (A i)) ∧
      Pairwise (Function.onFun Disjoint A) ∧ ⋃ i, A i = E ∧
        ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist (s x) (s y) < 1 / ((m : ℝ) + 1) :=
    fun m => exists_partition hs hΩ hE hEΩ (by positivity)
  choose n A hAm hAd hAU hAδ using hP
  refine ⟨n, A, hAm, hAd, fun k hk => ?_⟩
  have hΩ2 : IsCompact (Ω ×ˢ Ω) := hΩ.prod hΩ
  obtain ⟨M, hM⟩ := hΩ2.exists_bound_of_continuousOn hk.continuousOn
  have huc := Metric.uniformContinuousOn_iff.1 (hΩ2.uniformContinuousOn_of_continuous hk.continuousOn)
  have hkm : Measurable k := hk.measurable
  have hFm : StronglyMeasurable (Function.uncurry fun x y => k (s x, s y)) :=
    (hkm.comp (hs.prodMap hs)).stronglyMeasurable
  have hdm : Measurable fun x => k (s x, s x) := hkm.comp (hs.prodMk hs)
  have hsub : ∀ m i, ∀ x ∈ A m i, s x ∈ Ω := fun m i x hx => by
    have : x ∈ E := by rw [← hAU m]; exact Set.mem_iUnion.2 ⟨i, hx⟩
    exact hEΩ this
  have hint : ∀ m i, IntegrableOn (fun x => k (s x, s x)) (A m i) ν := fun m i =>
    (integrable_const M).mono' hdm.aestronglyMeasurable
      (ae_restrict_of_forall_mem (hAm m i) fun x hx => hM _ ⟨hsub m i x hx, hsub m i x hx⟩)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hV : 0 ≤ ν.real E := measureReal_nonneg
  obtain ⟨δ, hδ, hδk⟩ := huc (ε / (ν.real E + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun m hm => ?_⟩
  have hsmall : 1 / ((m : ℝ) + 1) < δ := lt_of_le_of_lt (Nat.one_div_le_one_div hm) hN
  have hE' : ∫ x in E, k (s x, s x) ∂ν = ∑ i, ∫ x in A m i, k (s x, s x) ∂ν := by
    conv_lhs => rw [← hAU m]
    exact integral_iUnion_fintype (hAm m) (hAd m) (hint m)
  have hVE : ν.real E = ∑ i, ν.real (A m i) := by
    rw [← hAU m]
    exact measureReal_iUnion_fintype (hAd m) (hAm m) (fun i => measure_ne_top _ _)
  rw [dist_eq_norm, hE', ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i, ‖(ν.real (A m i) : ℂ)⁻¹ * ∫ x in A m i, ∫ y in A m i, k (s x, s y) ∂ν ∂ν -
          ∫ x in A m i, k (s x, s x) ∂ν‖ := norm_sum_le _ _
    _ ≤ ∑ i, ε / (ν.real E + 1) * ν.real (A m i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      refine norm_mean_sub_le (ν := ν) (F := fun x y => k (s x, s y)) hFm (hAm m i) (M := M)
        (fun x hx y hy => hM _ ⟨hsub m i x hx, hsub m i y hy⟩) (fun x hx y hy => ?_)
      have hd : dist (s x, s y) (s x, s x) < δ := by
        rw [Prod.dist_eq, dist_self]
        exact max_lt hδ (lt_trans (hAδ m i y hy x hx) hsmall)
      have := hδk (s x, s y) ⟨hsub m i x hx, hsub m i y hy⟩ (s x, s x) ⟨hsub m i x hx, hsub m i x hx⟩ hd
      rw [dist_eq_norm] at this
      exact this.le
    _ = ε / (ν.real E + 1) * ν.real E := by rw [← Finset.mul_sum, ← hVE]
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

theorem tsum_setIntegral_eq (hs : MeasurableEmbedding s) {T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν} {k : Y × Y → ℂ}
    (hk : Continuous k) (hT : ∀ φ : Lp ℂ 2 ν, T φ =ᵐ[ν] fun x => ∫ y, k (s x, s y) * φ y ∂ν)
    {ι : Type*} {a b : ι → Lp ℂ 2 ν} (h : Summable fun j => ‖b j‖ * ‖a j‖)
    (hab : ∀ ψ φ, HasSum (fun j => ⟪ψ, a j⟫_ℂ * ⟪b j, φ⟫_ℂ) ⟪ψ, T φ⟫_ℂ)
    {Ω : Set Y} (hΩ : IsCompact Ω) {E : Set X} (hE : MeasurableSet E) (hEΩ : E ⊆ s ⁻¹' Ω) :
    ∑' j, ∫ x in E, ⟪b j x, a j x⟫_ℂ ∂ν = ∫ x in E, k (s x, s x) ∂ν := by
  classical
  have core1 : ∀ {A : Set X} (hA : MeasurableSet A) (v : Lp ℂ 2 ν),
      v = indicatorConstLp 2 hA (measure_ne_top ν A) (1 : ℂ) →
      ⟪v, T v⟫_ℂ = ∫ x in A, ∫ y in A, k (s x, s y) ∂ν ∂ν := by
    intro A hA v hv
    subst hv
    rw [L2.inner_indicatorConstLp_one]
    refine integral_congr_ae (ae_restrict_of_ae ((hT (indicatorConstLp 2 hA (measure_ne_top ν A) (1 : ℂ))).mono
      fun x hx => ?_))
    rw [hx]
    dsimp only
    rw [← integral_indicator hA]
    refine integral_congr_ae ((indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top ν A)
      (c := (1 : ℂ))).mono fun y hy => ?_)
    dsimp only
    rw [hy]
    by_cases hy' : y ∈ A <;> simp [hy']
  have core2 : ∀ {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (v w : Lp ℂ 2 ν),
      v = indicatorConstLp 2 hA (measure_ne_top ν A) (1 : ℂ) →
      w = indicatorConstLp 2 hB (measure_ne_top ν B) (1 : ℂ) → ⟪v, w⟫_ℂ = (ν.real (B ∩ A) : ℂ) := by
    intro A B hA hB v w hv hw
    subst hv hw
    rw [L2.inner_indicatorConstLp_one, setIntegral_indicatorConstLp hA]
    simp
  have core3 : ∀ {A : Set X} (hA : MeasurableSet A) {g h : Y → ℂ} {β α : Lp ℂ 2 ν},
      (β =ᵐ[ν] fun x => g (s x)) → (α =ᵐ[ν] fun x => h (s x)) → ∀ v : Lp ℂ 2 ν,
      v = indicatorConstLp 2 hA (measure_ne_top ν A) (1 : ℂ) →
      ⟪v, α⟫_ℂ * ⟪β, v⟫_ℂ = ∫ x in A, ∫ y in A, starRingEnd ℂ (g (s x)) * h (s y) ∂ν ∂ν := by
    intro A hA g h β α hβ hα v hv
    subst hv
    rw [← inner_conj_symm β, L2.inner_indicatorConstLp_one, L2.inner_indicatorConstLp_one,
      integral_congr_ae (ae_restrict_of_ae hα), integral_congr_ae (ae_restrict_of_ae hβ), ← integral_conj]
    simp_rw [integral_const_mul]
    rw [integral_mul_const]
    ring
  obtain ⟨n, A, hAm, hAd, hlim⟩ := exists_partitions (ν := ν) hs.measurable hΩ hE hEΩ
  obtain ⟨v, hv⟩ : ∃ v : ∀ m, Fin (n m) → Lp ℂ 2 ν,
      ∀ m i, v m i = indicatorConstLp 2 (hAm m i) (measure_ne_top ν _) (1 : ℂ) := ⟨_, fun _ _ => rfl⟩
  have hvv : ∀ m i, ⟪v m i, v m i⟫_ℂ = ((fun i => ν.real (A m i)) i : ℂ) := by
    intro m i
    rw [core2 (hAm m i) (hAm m i) _ _ (hv m i) (hv m i), Set.inter_self]
  have hvo : ∀ m i j, i ≠ j → ⟪v m i, v m j⟫_ℂ = 0 := by
    intro m i j hij
    rw [core2 (hAm m i) (hAm m j) _ _ (hv m i) (hv m j), ((hAd m hij).symm).inter_eq]
    simp
  have hP : ∀ m, ‖projSum (v m) (fun i => ν.real (A m i))‖ ≤ 1 := fun m =>
    norm_projSum_le (hvv m) (hvo m)

  have h1 : Tendsto (fun m => ∑ i, ((ν.real (A m i) : ℝ) : ℂ)⁻¹ * ⟪v m i, T (v m i)⟫_ℂ) atTop
      (𝓝 (∫ x in E, k (s x, s x) ∂ν)) := by
    refine (hlim k hk).congr fun m => Finset.sum_congr rfl fun i _ => ?_
    rw [core1 (hAm m i) _ (hv m i)]

  have h2 : ∀ m, ∑ i, ((ν.real (A m i) : ℝ) : ℂ)⁻¹ * ⟪v m i, T (v m i)⟫_ℂ =
      ∑' j, ⟪b j, projSum (v m) (fun i => ν.real (A m i)) (a j)⟫_ℂ := by
    intro m
    have hs' : HasSum (fun j => ∑ i, ((ν.real (A m i) : ℝ) : ℂ)⁻¹ * (⟪v m i, a j⟫_ℂ * ⟪b j, v m i⟫_ℂ))
        (∑ i, ((ν.real (A m i) : ℝ) : ℂ)⁻¹ * ⟪v m i, T (v m i)⟫_ℂ) :=
      hasSum_sum fun i _ => (hab (v m i) (v m i)).mul_left _
    rw [← hs'.tsum_eq]
    simp_rw [inner_projSum]

  have hq : Continuous (Function.uncurry fun (β α : Lp ℂ 2 ν) => ∫ x in E, ⟪β x, α x⟫_ℂ ∂ν) := by
    have heq : (Function.uncurry fun (β α : Lp ℂ 2 ν) => ∫ x in E, ⟪β x, α x⟫_ℂ ∂ν) =
        fun p : Lp ℂ 2 ν × Lp ℂ 2 ν => ⟪LpToLpRestrictCLM X ℂ ℂ ν 2 E p.1, LpToLpRestrictCLM X ℂ ℂ ν 2 E p.2⟫_ℂ := by
      funext p
      simp only [Function.uncurry]
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [LpToLpRestrictCLM_coeFn ℂ E p.1, LpToLpRestrictCLM_coeFn ℂ E p.2] with x hx1 hx2
      rw [hx1, hx2]
    rw [heq]
    exact ((LpToLpRestrictCLM X ℂ ℂ ν 2 E).continuous.comp continuous_fst).inner
      ((LpToLpRestrictCLM X ℂ ℂ ν 2 E).continuous.comp continuous_snd)
  have hS : ∀ β ∈ {a : Lp ℂ 2 ν | ∃ g : Y → ℂ, Continuous g ∧ a =ᵐ[ν] fun x => g (s x)},
      ∀ α ∈ {a : Lp ℂ 2 ν | ∃ g : Y → ℂ, Continuous g ∧ a =ᵐ[ν] fun x => g (s x)},
      Tendsto (fun m => ⟪β, projSum (v m) (fun i => ν.real (A m i)) α⟫_ℂ) atTop
        (𝓝 (∫ x in E, ⟪β x, α x⟫_ℂ ∂ν)) := by
    rintro β ⟨g, hg, hβ⟩ α ⟨h, hh, hα⟩
    have hk' : Continuous fun p : Y × Y => starRingEnd ℂ (g p.1) * h p.2 :=
      (Complex.continuous_conj.comp (hg.comp continuous_fst)).mul (hh.comp continuous_snd)
    have hE' : ∫ x in E, ⟪β x, α x⟫_ℂ ∂ν = ∫ x in E, starRingEnd ℂ (g (s x)) * h (s x) ∂ν := by
      refine integral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hβ, hα] with x hx1 hx2
      rw [hx1, hx2]
      simp [mul_comm]
    rw [hE']
    refine (hlim _ hk').congr fun m => ?_
    rw [inner_projSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [core3 (hAm m i) hβ hα _ (hv m i)]
  have h3 : Tendsto (fun m => ∑' j, ⟪b j, projSum (v m) (fun i => ν.real (A m i)) (a j)⟫_ℂ) atTop
      (𝓝 (∑' j, ∫ x in E, ⟪b j x, a j x⟫_ℂ ∂ν)) := by
    refine tendsto_tsum_of_dominated_convergence h
      (fun j => tendsto_inner_of_dense hP (dense_continuous hs) hq hS (b j) (a j))
      (Filter.Eventually.of_forall fun m j => ?_)
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact ((projSum (v m) _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hP m))
  exact tendsto_nhds_unique (h3.congr fun m => (h2 m).symm) h1

theorem trace_eq_integral_diagonal [SigmaCompactSpace Y] (hs : MeasurableEmbedding s)
    {T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν} (htr : IsTraceClass T) {k : Y × Y → ℂ}
    (hk : Continuous k) (hT : ∀ φ : Lp ℂ 2 ν, T φ =ᵐ[ν] fun x => ∫ y, k (s x, s y) * φ y ∂ν) :
    Integrable (fun x => k (s x, s x)) ν ∧ trace T = ∫ x, k (s x, s x) ∂ν := by
  classical
  obtain ⟨a, b, hsum, hab, htrace⟩ := exists_rankOne_expansion htr
  obtain ⟨d, hd, hE⟩ := exists_diagonal (ν := ν) hsum
  have hkm : Measurable (fun x => k (s x, s x)) :=
    hk.measurable.comp (hs.measurable.prodMk hs.measurable)
  have hΩc : ∀ n, IsCompact (closure (compactCovering Y n)) := fun n =>
    (isCompact_compactCovering Y n).closure
  have hEn : ∀ n, MeasurableSet (s ⁻¹' closure (compactCovering Y n)) := fun n =>
    isClosed_closure.measurableSet.preimage hs.measurable
  have hcover : ⋃ n, s ⁻¹' closure (compactCovering Y n) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, Set.mem_preimage]
    obtain ⟨n, hn⟩ := exists_mem_compactCovering (s x)
    exact ⟨n, subset_closure hn⟩
  have hint : ∀ n (A : Set X), MeasurableSet A → A ⊆ s ⁻¹' closure (compactCovering Y n) →
      ∫ x in A, d x ∂ν = ∫ x in A, k (s x, s x) ∂ν := by
    intro n A hA hAE
    rw [← (hE A).tsum_eq]
    exact tsum_setIntegral_eq hs hk hT hsum hab (hΩc n) hA hAE
  have hae : ∀ n, d =ᵐ[ν.restrict (s ⁻¹' closure (compactCovering Y n))] fun x => k (s x, s x) := by
    intro n
    obtain ⟨M, hM⟩ := ((hΩc n).prod (hΩc n)).exists_bound_of_continuousOn hk.continuousOn
    have hkdint : Integrable (fun x => k (s x, s x)) (ν.restrict (s ⁻¹' closure (compactCovering Y n))) :=
      Measure.integrableOn_of_bounded (M := M) (measure_ne_top _ _) hkm.aestronglyMeasurable
        ((ae_restrict_iff' (hEn n)).2 (Filter.Eventually.of_forall fun x hx => hM _ ⟨hx, hx⟩))
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun A _ _ => hd.restrict.integrableOn)
      (fun A _ _ => hkdint.integrableOn) ?_
    intro A hA _
    rw [Measure.restrict_restrict hA]
    exact hint n (A ∩ _) (hA.inter (hEn n)) Set.inter_subset_right
  have hae' : d =ᵐ[ν] fun x => k (s x, s x) := by
    have h := (ae_restrict_iUnion_iff (μ := ν) (fun n => s ⁻¹' closure (compactCovering Y n))
      (fun x => d x = k (s x, s x))).2 hae
    rwa [hcover, Measure.restrict_univ] at h
  refine ⟨hd.congr hae', ?_⟩
  have h2 := hE Set.univ
  simp only [Measure.restrict_univ] at h2
  rw [← htrace.tsum_eq, ← integral_congr_ae hae', ← h2.tsum_eq]
  rfl

end Measure

theorem traceIsDiagonal_Rop {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    [IsFiniteMeasure (quotMeasure Γ μ)] {f : G → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (htr : IsTraceClass (Rop Γ μ f)) : TraceIsDiagonal (ν := quotMeasure Γ μ) (Rop Γ μ f) (kernelQ Γ f) := by
  let _ : PseudoMetricSpace G := TopologicalSpace.pseudoMetrizableSpacePseudoMetric G
  have hint : Integrable f μ := hf.integrable_of_hasCompactSupport hc
  have hkq : ∀ p q : Quot Γ, kernelQ Γ f p q = kernel Γ f (sec Γ p) (sec Γ q) := by
    intro p q
    have e1 : mk Γ p.out = mk Γ (sec Γ p) := by rw [mk_sec]; exact Quotient.out_eq p
    have e2 : mk Γ q.out = mk Γ (sec Γ q) := by rw [mk_sec]; exact Quotient.out_eq q
    calc kernelQ Γ f p q = kernel Γ f p.out q.out := rfl
      _ = kernel Γ f (sec Γ p) q.out := (leftInv_kernel_left f q.out).eq_of_mk_eq e1
      _ = kernel Γ f (sec Γ p) (sec Γ q) := (leftInv_kernel_right f (sec Γ p)).eq_of_mk_eq e2
  have hT : ∀ φ : Lp ℂ 2 (quotMeasure Γ μ), Rop Γ μ f φ =ᵐ[quotMeasure Γ μ]
      fun x => ∫ y, (fun p : G × G => kernel Γ f p.1 p.2) (sec Γ x, sec Γ y) * φ y ∂(quotMeasure Γ μ) := by
    intro φ
    refine ae_quotMeasure_iff.2 ?_
    have h1 := (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR G Γ μ f hint φ).2
    filter_upwards [h1] with g hg
    have h2 := (GlobalTheory.AutomorphicL2KernelIntegral.convR_eq_integral_kernelQ G Γ μ f hf hc φ g).2
    change Rop Γ μ f φ (mk Γ g) = convR μ f (lift Γ φ) g at hg
    rw [hg, h2]
    refine integral_congr_ae (.of_forall fun q => ?_)
    simp only
    rw [hkq]
  obtain ⟨hI, htrace⟩ := trace_eq_integral_diagonal (ν := quotMeasure Γ μ) measurableEmbedding_sec htr
    (GlobalTheory.AutomorphicL2KernelContinuous.continuous_kernel hf hc) hT
  have hfun : (fun x => kernelQ Γ f x x) = fun x => kernel Γ f (sec Γ x) (sec Γ x) := funext fun x => hkq x x
  unfold TraceIsDiagonal
  refine ⟨htr, ?_, ?_⟩
  · rw [hfun]; exact hI
  · rw [htrace, hfun]

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem RopG_eq_comp {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    {f : GA D V → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (h : MapsIntoCusp V μ (starFn f)) :
    RopG V μ f = (L2cusp V μ).subtypeL ∘L RcuspOp V μ f ∘L (L2cusp V μ).orthogonalProjection := by
  have hint : Integrable f μ := hf.integrable_of_hasCompactSupport hc
  ext1 F
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [coe_RcuspOp V μ hint]
  have hperp : F - ((L2cusp V μ).orthogonalProjection F : DividedPowerChartLift V μ) ∈ (L2cusp V μ)ᗮ := by
    exact Submodule.sub_starProjection_mem_orthogonal (K := L2cusp V μ) F
  have hz : RopG V μ f (F - ((L2cusp V μ).orthogonalProjection F : DividedPowerChartLift V μ)) = 0 := by
    apply ext_inner_left ℂ
    intro G
    rw [inner_zero_right]
    change ⟪G, Rop (GQ V) μ f _⟫_ℂ = 0
    rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_Rop hf hc]
    exact Submodule.inner_right_of_mem_orthogonal (h G) hperp
  rw [map_sub, sub_eq_zero] at hz
  exact hz

end GlobalTheory.TraceDiagonal

end
