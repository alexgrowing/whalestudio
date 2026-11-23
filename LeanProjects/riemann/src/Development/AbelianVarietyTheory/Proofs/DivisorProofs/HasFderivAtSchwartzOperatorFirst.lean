import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslateTaylorSecondOrderStatement
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

noncomputable section

open Filter Topology Asymptotics

namespace GlobalTheory.SchwartzFstOp

variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sliceCLM_add_eq (x' v : V') (f : 𝓢(V × V', ℂ)) :
    sliceCLM (x' + v) f = sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f) := by
  ext x
  simp [SchwartzMap.compSubConstCLM_apply]

theorem remainder_bound (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (x' : V') :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : V', ‖v‖ ≤ 1 → ∀ z : W,
      ‖T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f)) z‖
        ≤ K * ‖v‖ ^ 2 := by
  let q : Seminorm ℂ 𝓢(V × V', ℂ) :=
    (SchwartzMap.seminorm ℂ 0 0).comp (T.comp (sliceCLM x')).toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℂ W E).continuous_seminorm (0, 0)).comp (T.comp (sliceCLM x')).continuous
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (V × V') ℂ) q hq
  choose D hD using fun i : ℕ × ℕ => GlobalTheory.T.schwartz_translate_taylor_second_order f i.1 i.2
  refine ⟨(C : ℝ) * ∑ i ∈ s, |D i|, by positivity, fun v hv z => ?_⟩
  set g := SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f with hg
  have ha : ‖((0 : V), v)‖ = ‖v‖ := by simp [Prod.norm_def]
  have h1 : ‖T (sliceCLM x' g) z‖ ≤ q g := SchwartzMap.norm_le_seminorm ℂ _ _
  have h2 : q g ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g := by
    have := hC g
    simpa [Seminorm.smul_apply, NNReal.smul_def] using this
  have h3 : (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g ≤ (∑ i ∈ s, |D i|) * ‖v‖ ^ 2 := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i hi
    have hDi := hD i ((0 : V), v) (by rw [ha]; exact hv)
    rw [ha] at hDi
    calc schwartzSeminormFamily ℂ (V × V') ℂ i g ≤ D i * ‖v‖ ^ 2 := hDi
      _ ≤ |D i| * ‖v‖ ^ 2 := by gcongr; exact le_abs_self _
      _ ≤ (∑ j ∈ s, |D j|) * ‖v‖ ^ 2 := by
          gcongr; exact Finset.single_le_sum (fun j _ => abs_nonneg (D j)) hi
  calc ‖T (sliceCLM x' g) z‖ ≤ q g := h1
    _ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g := h2
    _ ≤ (C : ℝ) * ((∑ i ∈ s, |D i|) * ‖v‖ ^ 2) := by gcongr
    _ = (C : ℝ) * (∑ i ∈ s, |D i|) * ‖v‖ ^ 2 := by ring

theorem opFst_add_decomp (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y w : W) (x' v : V') :
    opFst T f (y + w, x' + v) =
      T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f)) (y + w)
        + T (sliceCLM x' f) (y + w) + T (sliceCLM x' (lineSnd v f)) (y + w) := by
  rw [opFst_apply, sliceCLM_add_eq]
  conv_lhs => rw [show SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f
      = (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f) + f + lineSnd v f by abel]
  simp only [map_add, SchwartzMap.add_apply]

theorem hasFDerivAt_opFst [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ))
    (y : W) (x' : V') :
    HasFDerivAt (opFst T f) ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V')
      + (dSndCLM T f (y, x')).comp (ContinuousLinearMap.snd ℝ W V')) (y, x') := by
  have hA : HasFDerivAt (fun q : W × V' => T (sliceCLM x' f) q.1)
      ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V')) (y, x') :=
    ((T (sliceCLM x' f)).differentiableAt.hasFDerivAt).comp (y, x') hasFDerivAt_fst
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hA ⊢
  have hcont : Continuous fun z : W => dSndCLM T f (z, x') := by
    rw [continuous_clm_apply]
    intro v
    exact (T (sliceCLM x' (lineSnd v f))).continuous
  have hB : (fun p : W × V' => dSndCLM T f (y + p.1, x') p.2 - dSndCLM T f (y, x') p.2)
      =o[𝓝 0] fun p => p := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have ht : Tendsto (fun p : W × V' => dSndCLM T f (y + p.1, x')) (𝓝 0) (𝓝 (dSndCLM T f (y, x'))) := by
      have : Tendsto (fun p : W × V' => y + p.1) (𝓝 0) (𝓝 y) := by
        have := (tendsto_const_nhds (x := y)).add ((continuous_fst.tendsto (0 : W × V')))
        simpa using this
      exact (hcont.tendsto y).comp this
    filter_upwards [(Metric.tendsto_nhds.mp ht) c hc] with p hp
    rw [← ContinuousLinearMap.sub_apply]
    calc _ ≤ ‖dSndCLM T f (y + p.1, x') - dSndCLM T f (y, x')‖ * ‖p.2‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖p‖ := by
          gcongr
          · rw [← dist_eq_norm]; exact hp.le
          · exact norm_snd_le p
  obtain ⟨K, hK0, hK⟩ := remainder_bound T f x'
  have hC : (fun p : W × V' =>
      T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), p.2)) f - f - lineSnd p.2 f)) (y + p.1))
      =o[𝓝 0] fun p => p := by
    have h1 : (fun p : W × V' =>
        T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), p.2)) f - f - lineSnd p.2 f)) (y + p.1))
        =O[𝓝 0] fun p : W × V' => ‖p‖ ^ 2 := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨K, ?_⟩
      filter_upwards [Metric.closedBall_mem_nhds (0 : W × V') one_pos] with p hp
      rw [Metric.mem_closedBall, dist_zero_right] at hp
      calc _ ≤ K * ‖p.2‖ ^ 2 := hK p.2 ((norm_snd_le p).trans hp) _
        _ ≤ K * ‖p‖ ^ 2 := by gcongr; exact norm_snd_le p
        _ = K * ‖‖p‖ ^ 2‖ := by rw [norm_pow, norm_norm]
    exact h1.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine ((hA.add hB).add hC).congr_left (fun p => ?_)
  obtain ⟨w, v⟩ := p
  simp only [Prod.mk_add_mk]
  rw [opFst_add_decomp]
  simp only [opFst_apply, dSndCLM_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  abel

end GlobalTheory.SchwartzFstOp
