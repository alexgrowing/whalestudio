import Mathlib

noncomputable def UpperTheory.Reformulated.B.Yzb8.SelfDual :
    {V : Type} →
      [AddCommGroup V] → [TopologicalSpace V] → [inst : MeasurableSpace V] → MeasureTheory.Measure V → (V → V → ℂ) → Prop :=
    fun {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : MeasureTheory.Measure V) (χ : V → V → ℂ) ↦
      μ.IsAddHaarMeasure ∧
        ∀ (Φ : V → ℂ),
          Continuous Φ →
            HasCompactSupport Φ →
              MeasureTheory.Integrable (fun (y : V) ↦ ∫ (x : V), Φ x * χ x y ∂μ) μ →
                ∀ (z : V), ∫ (y : V), (∫ (x : V), Φ x * χ x y ∂μ) * χ y z ∂μ = Φ (-z)

namespace UpperTheory.Reformulated.B.Yzb8

open MeasureTheory FourierTransform
open scoped NNReal ENNReal

section aux

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private noncomputable def ee (t : ℝ) : ℂ :=
  Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑t : ℂ))

private lemma integral_mul_ee (f : E → ℂ) (w : E) :
    ∫ u, f u * ee (inner ℝ u w) = 𝓕 f (-w) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [ee, inner_neg_right, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

private lemma integral_mul_ee' (f : E → ℂ) (w : E) :
    ∫ u, f u * ee (inner ℝ u w) = 𝓕⁻ f w := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [ee, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

private lemma emb (T : V ≃L[ℝ] E) : MeasurableEmbedding (T.symm : E → V) :=
  T.symm.toHomeomorph.measurableEmbedding

private lemma inner_eq (T S : V ≃L[ℝ] E) (b : V → V → ℝ)
    (hb : ∀ x y, b x y = inner ℝ (T x) (S y)) (Φ : V → ℂ) (y : V) :
    ∫ x, Φ x * ee (b x y) ∂(Measure.map (T.symm : E → V) volume) =
      𝓕 (fun u => Φ (T.symm u)) (-(S y)) := by
  rw [(emb T).integral_map, ← integral_mul_ee]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp [hb]

private lemma outer_eq (T S : V ≃L[ℝ] E) (b : V → V → ℝ)
    (hb : ∀ x y, b x y = inner ℝ (T x) (S y)) (hs : ∀ x y, b x y = b y x)
    (H : E → ℂ) (z : V) :
    ∫ y, H (-(S y)) * ee (b y z) ∂(Measure.map (S.symm : E → V) volume) =
      𝓕⁻ H (-(T z)) := by
  rw [(emb S).integral_map, ← integral_mul_ee',
    ← integral_neg_eq_self (fun u => H u * ee (inner ℝ u (-(T z))))]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp [hs _ z, hb, real_inner_comm]

private lemma main (T S : V ≃L[ℝ] E) (b : V → V → ℝ)
    (hb : ∀ x y, b x y = inner ℝ (T x) (S y)) (hs : ∀ x y, b x y = b y x)
    (k a : ℝ≥0) (hk0 : k ≠ 0) (ha : a ≠ 0)
    (hk : Measure.map (S.symm : E → V) volume = k • Measure.map (T.symm : E → V) volume)
    (Φ : V → ℂ) (hc : Continuous Φ) (hcs : HasCompactSupport Φ) :
    (Integrable (fun y => ∫ x, Φ x * ee (b x y) ∂(a • Measure.map (T.symm : E → V) volume))
        (a • Measure.map (T.symm : E → V) volume) ↔
      Integrable (𝓕 (fun u => Φ (T.symm u))) volume) ∧
    (Integrable (𝓕 (fun u => Φ (T.symm u))) volume → ∀ z,
      ∫ y, (∫ x, Φ x * ee (b x y) ∂(a • Measure.map (T.symm : E → V) volume)) * ee (b y z)
        ∂(a • Measure.map (T.symm : E → V) volume) = ((a ^ 2 / k : ℝ≥0) : ℂ) * Φ (-z)) := by
  set G : E → ℂ := fun u => Φ (T.symm u) with hG
  have h1 : ∀ y, ∫ x, Φ x * ee (b x y) ∂(a • Measure.map (T.symm : E → V) volume) =
      (a : ℂ) * 𝓕 G (-(S y)) := by
    intro y
    rw [integral_smul_nnreal_measure, inner_eq T S b hb, NNReal.smul_def, Complex.real_smul]
  have hμ : a • Measure.map (T.symm : E → V) volume =
      (a / k) • Measure.map (S.symm : E → V) volume := by
    rw [hk, smul_smul, div_mul_cancel₀ _ hk0]
  have hak : ((a / k : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simpa using div_ne_zero ha hk0
  simp only [h1]
  rw [hμ]
  refine ⟨?_, ?_⟩
  · have : Integrable (fun y => (a : ℂ) * 𝓕 G (-(S y))) ((a / k) • Measure.map (S.symm : E → V) volume) ↔
        Integrable (fun y => (a : ℂ) * 𝓕 G (-(S y))) (Measure.map (S.symm : E → V) volume) :=
      integrable_smul_measure hak ENNReal.coe_ne_top
    rw [this, (emb S).integrable_map_iff]
    have ha' : IsUnit (a : ℂ) := by simpa using ha
    have e1 : ((fun y => (a : ℂ) * 𝓕 G (-(S y))) ∘ (S.symm : E → V)) =
        fun w => (a : ℂ) * (fun w => 𝓕 G (-w)) w := by
      funext w; simp
    rw [e1, integrable_const_mul_iff ha']
    exact ⟨fun h => by simpa using h.comp_neg, fun h => h.comp_neg⟩
  · intro hint z
    have e2 : ∀ y, (a : ℂ) * 𝓕 G (-(S y)) * ee (b y z) = (a : ℂ) * (𝓕 G (-(S y)) * ee (b y z)) :=
      fun y => mul_assoc _ _ _
    simp only [e2]
    have hGc : Continuous G := hc.comp T.symm.continuous
    have hGs : HasCompactSupport G := hcs.comp_homeomorph T.symm.toHomeomorph
    have hinv : 𝓕⁻ (𝓕 G) = G :=
      hGc.fourierInv_fourier_eq (hGc.integrable_of_hasCompactSupport hGs) hint
    rw [integral_smul_nnreal_measure, integral_const_mul, outer_eq T S b hb hs,
      hinv, NNReal.smul_def, Complex.real_smul]
    have e3 : G (-(T z)) = Φ (-z) := by simp [hG]
    rw [e3]
    push_cast
    field_simp

private lemma exists_bump : ∃ G : E → ℂ, Continuous G ∧ HasCompactSupport G ∧ G 0 ≠ 0 ∧
    Integrable (𝓕 G) volume := by
  let f : ContDiffBump (0 : E) := default
  have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ((f x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp f.contDiff
  have hcs : HasCompactSupport (fun x => ((f x : ℝ) : ℂ)) :=
    f.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  refine ⟨fun x => ((f x : ℝ) : ℂ), hd.continuous, hcs, ?_, ?_⟩
  · have h1 : f 0 = 1 := f.one_of_mem_closedBall (by simp [f.rIn_pos.le])
    simp [h1]
  · exact (𝓕 (hcs.toSchwartzMap hd)).integrable

end aux

end UpperTheory.Reformulated.B.Yzb8

open MeasureTheory FourierTransform UpperTheory.Reformulated.B.Yzb8
open scoped NNReal ENNReal
