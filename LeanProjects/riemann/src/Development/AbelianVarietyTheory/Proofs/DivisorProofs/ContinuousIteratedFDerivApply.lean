import Mathlib
open MeasureTheory

namespace GlobalTheory.SchwInt

theorem integrable_of_zero_outside {P E : Type} [TopologicalSpace P] [MeasurableSpace P]
    [OpensMeasurableSpace P] [SecondCountableTopology P] [NormedAddCommGroup E]
    (μ : Measure P) [IsFiniteMeasureOnCompacts μ] {f : P → E} (hf : Continuous f)
    {C : Set P} (hC : IsCompact C) (h0 : ∀ p ∉ C, f p = 0) : Integrable f μ := by
  obtain ⟨M, hM⟩ := (hC.image hf).isBounded.exists_norm_le
  have hM' : ∀ p, ‖f p‖ ≤ max M 0 := by
    intro p
    by_cases hp : p ∈ C
    · exact (hM _ ⟨p, hp, rfl⟩).trans (le_max_left _ _)
    · simp [h0 p hp]
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := C) ?_ h0
  exact Measure.integrableOn_of_bounded (M := max M 0) hC.measure_lt_top.ne
    hf.aestronglyMeasurable (Filter.Eventually.of_forall hM')

noncomputable def iterEvalCLM {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) (x : V) :
    SchwartzMap V ℂ →L[ℂ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => iteratedFDeriv ℝ n f x)
    (fun f g => by
      show iteratedFDeriv ℝ n (⇑f + ⇑g) x = _
      exact iteratedFDeriv_add_apply (f.smooth n).contDiffAt (g.smooth n).contDiffAt)
    (fun a f => by
      show iteratedFDeriv ℝ n (a • ⇑f) x = _
      exact iteratedFDeriv_const_smul_apply (f.smooth n).contDiffAt)
    ⟨{(0, n)}, 1, zero_le_one, fun f => by
      simpa [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] using f.le_seminorm ℂ 0 n x⟩

@[simp] theorem iterEvalCLM_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) (x : V)
    (f : SchwartzMap V ℂ) : iterEvalCLM n x f = iteratedFDeriv ℝ n f x := rfl

theorem continuous_iteratedFDeriv_apply {V P : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace P] {G : P → SchwartzMap V ℂ} (hG : Continuous G) (n : ℕ) (x : V) :
    Continuous fun p => iteratedFDeriv ℝ n (G p) x :=
  (iterEvalCLM n x).continuous.comp hG

theorem continuous_apply {V P : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace P] {G : P → SchwartzMap V ℂ} (hG : Continuous G) (x : V) :
    Continuous fun p => G p x :=
  ((BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)).continuous.comp hG

end GlobalTheory.SchwInt
