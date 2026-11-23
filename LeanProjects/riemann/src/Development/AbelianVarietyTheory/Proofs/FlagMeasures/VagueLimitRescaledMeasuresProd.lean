import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConst

open Filter Topology

def prodFns (V W : Type) [TopologicalSpace V] [TopologicalSpace W] : Submonoid C(V × W, ℝ) where
  carrier := {g | ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2}
  one_mem' := ⟨1, 1, fun z => by simp⟩
  mul_mem' := by
    rintro g h ⟨a, b, hg⟩ ⟨a', b', hh⟩
    exact ⟨a * a', b * b', fun z => by simp [hg, hh]; ring⟩

theorem prodFns_separates (V W : Type) [MetricSpace V] [MetricSpace W] :
    (Algebra.adjoin ℝ (prodFns V W : Set C(V × W, ℝ))).SeparatesPoints := by
  intro p q hpq
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext h1 h)
    let g : C(V × W, ℝ) := ⟨fun z => dist z.2 q.2, by fun_prop⟩
    have hg : g ∈ (prodFns V W : Set C(V × W, ℝ)) := by
      show ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2
      exact ⟨1, ⟨fun y => dist y q.2, by fun_prop⟩, fun z => by simp [g]⟩
    refine ⟨g, ⟨g, Algebra.subset_adjoin hg, rfl⟩, ?_⟩
    simpa [g] using h2
  · let g : C(V × W, ℝ) := ⟨fun z => dist z.1 q.1, by fun_prop⟩
    have hg : g ∈ (prodFns V W : Set C(V × W, ℝ)) := by
      show ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2
      exact ⟨⟨fun x => dist x q.1, by fun_prop⟩, 1, fun z => by simp [g]⟩
    refine ⟨g, ⟨g, Algebra.subset_adjoin hg, rfl⟩, ?_⟩
    simpa [g] using h1

theorem hasCompactSupport_prod_mul {V W : Type} [MetricSpace V] [MetricSpace W] {a : V → ℝ} {b : W → ℝ}
    (ha : HasCompactSupport a) (hb : HasCompactSupport b) :
    HasCompactSupport (fun z : V × W => a z.1 * b z.2) := by
  refine HasCompactSupport.intro (ha.isCompact.prod hb.isCompact) fun z hz => ?_
  rcases not_and_or.mp (show ¬(z.1 ∈ tsupport a ∧ z.2 ∈ tsupport b) from hz) with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [image_eq_zero_of_notMem_tsupport h]

theorem tendsto_integral_of_prod {ι V W : Type} [MetricSpace V] [MetricSpace W] [ProperSpace V] [ProperSpace W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W] (l : Filter ι)
    (M : ι → Measure (V × W)) (M₀ : Measure (V × W)) [∀ i, IsFiniteMeasureOnCompacts (M i)]
    [IsFiniteMeasureOnCompacts M₀]
    (h : ∀ (a : V → ℝ) (b : W → ℝ), Continuous a → HasCompactSupport a → Continuous b → HasCompactSupport b →
      Tendsto (fun i => ∫ z, a z.1 * b z.2 ∂M i) l (𝓝 (∫ z, a z.1 * b z.2 ∂M₀)))
    (F : V × W → ℝ) (hF : Continuous F) (hFc : HasCompactSupport F) :
    Tendsto (fun i => ∫ z, F z ∂M i) l (𝓝 (∫ z, F z ∂M₀)) := by
  have hKc : IsCompact (tsupport F) := hFc
  obtain ⟨χ₁, h1K, -, h1c, h1b⟩ := exists_continuous_one_zero_of_isCompact
    (hKc.image continuous_fst) isClosed_empty (Set.disjoint_empty _)
  obtain ⟨χ₂, h2K, -, h2c, h2b⟩ := exists_continuous_one_zero_of_isCompact
    (hKc.image continuous_snd) isClosed_empty (Set.disjoint_empty _)
  set χ : V × W → ℝ := fun z => χ₁ z.1 * χ₂ z.2 with hχ
  have hχc : Continuous χ := (χ₁.continuous.comp continuous_fst).mul (χ₂.continuous.comp continuous_snd)
  have hχs : HasCompactSupport χ := hasCompactSupport_prod_mul h1c h2c
  have hχ0 : ∀ z, 0 ≤ χ z := fun z => mul_nonneg (h1b _).1 (h2b _).1
  have hχF : ∀ z, χ z * F z = F z := by
    intro z
    by_cases hz : z ∈ tsupport F
    · have e1 : χ₁ z.1 = 1 := by simpa using h1K ⟨z, hz, rfl⟩
      have e2 : χ₂ z.2 = 1 := by simpa using h2K ⟨z, hz, rfl⟩
      simp [hχ, e1, e2]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hX : IsCompact (tsupport χ₁ ×ˢ tsupport χ₂) := h1c.isCompact.prod h2c.isCompact
  have hχX : ∀ z, z ∉ tsupport χ₁ ×ˢ tsupport χ₂ → χ z = 0 := by
    intro z hz
    rcases not_and_or.mp (show ¬(z.1 ∈ tsupport χ₁ ∧ z.2 ∈ tsupport χ₂) from hz) with h | h
    · simp [hχ, image_eq_zero_of_notMem_tsupport h]
    · simp [hχ, image_eq_zero_of_notMem_tsupport h]
  have hint : ∀ (G : C(V × W, ℝ)) (m : Measure (V × W)) [IsFiniteMeasureOnCompacts m],
      Integrable (fun z => χ z * G z) m := fun G m _ =>
    (hχc.mul G.continuous).integrable_of_hasCompactSupport (hχs.mul_right (f' := G))
  have key : ∀ G ∈ Algebra.adjoin ℝ (prodFns V W : Set C(V × W, ℝ)),
      Tendsto (fun i => ∫ z, χ z * G z ∂M i) l (𝓝 (∫ z, χ z * G z ∂M₀)) := by
    intro G hG
    have hG' : G ∈ Submodule.span ℝ (prodFns V W : Set C(V × W, ℝ)) := by
      have : G ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ (prodFns V W : Set C(V × W, ℝ))) := hG
      rwa [Algebra.adjoin_eq_span, Submonoid.closure_eq] at this
    clear hG
    induction hG' using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, b, hab⟩ : ∃ a : C(V, ℝ), ∃ b : C(W, ℝ), ∀ z, g z = a z.1 * b z.2 := hg
      have e : (fun z => χ z * g z) = fun z : V × W => (χ₁ z.1 * a z.1) * (χ₂ z.2 * b z.2) := by
        funext z
        rw [hab, hχ]
        ring
      rw [e]
      exact h (fun x => χ₁ x * a x) (fun y => χ₂ y * b y) (χ₁.continuous.mul a.continuous)
        (h1c.mul_right (f' := a)) (χ₂.continuous.mul b.continuous) (h2c.mul_right (f' := b))
    | zero =>
      have e : ∀ m : Measure (V × W), ∫ z, χ z * (0 : C(V × W, ℝ)) z ∂m = 0 := fun m => by simp
      simp only [e]
      exact tendsto_const_nhds
    | add g g' _ _ hg hg' =>
      have e : ∀ (m : Measure (V × W)) [IsFiniteMeasureOnCompacts m],
          ∫ z, χ z * (g + g') z ∂m = ∫ z, χ z * g z ∂m + ∫ z, χ z * g' z ∂m := by
        intro m _
        rw [← integral_add (hint g m) (hint g' m)]
        congr 1
        funext z
        simp [mul_add]
      rw [e M₀]
      exact (hg.add hg').congr fun i => (e (M i)).symm
    | smul k g _ hg =>
      have e : ∀ m : Measure (V × W), ∫ z, χ z * (k • g) z ∂m = k * ∫ z, χ z * g z ∂m := by
        intro m
        rw [← integral_const_mul]
        congr 1
        funext z
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      rw [e M₀]
      exact (hg.const_mul k).congr fun i => (e (M i)).symm
  obtain ⟨L, hLdef⟩ : ∃ L, L = ∫ z, χ z ∂M₀ := ⟨_, rfl⟩
  have hL : Tendsto (fun i => ∫ z, χ z ∂M i) l (𝓝 L) := by
    rw [hLdef]
    exact h χ₁ χ₂ χ₁.continuous h1c χ₂.continuous h2c
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : (0 : ℝ) < |L| + 1 := by positivity
  set δ := ε / 3 / (|L| + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ3 : δ * (|L| + 1) = ε / 3 := div_mul_cancel₀ _ (ne_of_gt hpos)
  obtain ⟨G, hGA, hGK⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (prodFns_separates V W) ⟨F, hF⟩ hX hδpos
  have hb : ∀ z, ‖F z - χ z * G z‖ ≤ δ * χ z := by
    intro z
    have e : F z - χ z * G z = χ z * (F z - G z) := by rw [mul_sub, hχF]
    rw [e, norm_mul, Real.norm_of_nonneg (hχ0 z)]
    by_cases hz : z ∈ tsupport χ₁ ×ˢ tsupport χ₂
    · have hz' : ‖F z - G z‖ ≤ δ := by
        have := (hGK z hz).le
        rwa [norm_sub_rev] at this
      calc χ z * ‖F z - G z‖ ≤ χ z * δ := mul_le_mul_of_nonneg_left hz' (hχ0 z)
        _ = δ * χ z := mul_comm _ _
    · simp [hχX z hz]
  have hbI : ∀ (m : Measure (V × W)) [IsFiniteMeasureOnCompacts m],
      ‖∫ z, F z ∂m - ∫ z, χ z * G z ∂m‖ ≤ δ * ∫ z, χ z ∂m := by
    intro m _
    rw [← integral_sub (hF.integrable_of_hasCompactSupport hFc) (hint G m), ← integral_const_mul]
    exact norm_integral_le_of_norm_le ((hχc.integrable_of_hasCompactSupport hχs).const_mul δ)
      (Eventually.of_forall hb)
  filter_upwards [hL.eventually (gt_mem_nhds (lt_add_one L)),
    Metric.tendsto_nhds.mp (key G hGA) (ε / 3) (by positivity)] with i hi1 hi2
  have e1 := hbI (M i)
  have e2 := hbI M₀
  rw [← hLdef] at e2
  rw [Real.norm_eq_abs, abs_le] at e1 e2
  rw [Real.dist_eq, abs_lt] at hi2 ⊢
  have h3 : δ * ∫ z, χ z ∂M i < ε / 3 := by
    calc δ * ∫ z, χ z ∂M i < δ * (|L| + 1) :=
          mul_lt_mul_of_pos_left (by linarith [le_abs_self L]) hδpos
      _ = ε / 3 := hδ3
  have h4 : δ * L < ε / 3 := by
    calc δ * L ≤ δ * |L| := mul_le_mul_of_nonneg_left (le_abs_self L) hδpos.le
      _ < δ * (|L| + 1) := by linarith
      _ = ε / 3 := hδ3
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hi2.1, hi2.2]

theorem vag_prod (α β V W : Type) [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : α → V) (c' : β → W) (lam : Measure V) (lam' : Measure W)
    [IsLocallyFiniteMeasure lam] [IsLocallyFiniteMeasure lam'] (d d' : ℕ) (hc : Measurable c) (hc' : Measurable c')
    (h : Vag μ c lam d) (h' : Vag ν c' lam' d') :
    Vag (μ.prod ν) (Prod.map c c') (lam.prod lam') (d + d') := by
  intro φ hφ hφc
  let M : ℝ → Measure (V × W) := fun r =>
    Real.toNNReal ((r ^ (d + d'))⁻¹) • (μ.prod ν).map (fun g => (r⁻¹ • c g.1, r⁻¹ • c' g.2))
  have : ∀ r, IsFiniteMeasureOnCompacts (M r) := fun r => by dsimp only [M]; infer_instance
  have hmeas : ∀ r : ℝ, Measurable (fun g : α × β => (r⁻¹ • c g.1, r⁻¹ • c' g.2)) := fun r =>
    (((continuous_const_smul r⁻¹).measurable.comp hc).comp measurable_fst).prodMk
      (((continuous_const_smul r⁻¹).measurable.comp hc').comp measurable_snd)
  have hint : ∀ r : ℝ, 0 < r → ∀ f : V × W → ℝ, Continuous f →
      ∫ z, f z ∂M r = (r ^ (d + d'))⁻¹ * ∫ g, f (r⁻¹ • c g.1, r⁻¹ • c' g.2) ∂(μ.prod ν) := by
    intro r hr f hf
    dsimp only [M]
    rw [integral_smul_nnreal_measure, integral_map (hmeas r).aemeasurable hf.aestronglyMeasurable,
      NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (by positivity)]
  have key := tendsto_integral_of_prod (nhdsWithin (0 : ℝ) (Set.Ioi 0)) M (lam.prod lam') ?_ φ hφ hφc
  · refine key.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [hint r hr φ hφ]
    rfl
  · intro a b ha hac hb hbc
    have hprod := (h a ha hac).mul (h' b hb hbc)
    rw [integral_prod_mul a b]
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [hint r hr (fun z => a z.1 * b z.2) ((ha.comp continuous_fst).mul (hb.comp continuous_snd))]
    have e := integral_prod_mul (μ := μ) (ν := ν) (fun x => a (r⁻¹ • c x)) (fun y => b (r⁻¹ • c' y))
    simp only at e ⊢
    rw [e, pow_add, mul_inv]
    ring

end GlobalTheory.IwConst
