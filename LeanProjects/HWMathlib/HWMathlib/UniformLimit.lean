import Mathlib

open Set Filter Topology MeasureTheory

/-- 定理 1.42（极限函数的逐项积分定理）

设 `a ≤ b`，`{fₙ}` 是 `[a, b]` 上的一列可积函数。
若 `fₙ` 在 `[a, b]` 上一致收敛于 `F`，则 `F` 也在 `[a, b]` 上可积，
且极限与积分可交换：
  `∫ x in a..b, lim fₙ x = lim ∫ x in a..b, fₙ x`。

形式化说明：
- 教材中的 "Riemann 可积" 在 Lean 中对应 `IntervalIntegrable · volume a b`
  （Mathlib 的区间积分是 Bochner 积分；对 Riemann 可积函数二者取值一致，
  而一致收敛的极限保持可积性用 Bochner/控制收敛的语言最为自然）。
- 教材证明分两步：(i) 用 Lebesgue 判别法（不连续点集是零测集）证极限函数可积；
  (ii) 用 ε-估计证积分号下取极限。
  在 Lean 中，(i) 改为：一致收敛给出一致界 `‖F‖ ≤ ‖f_N‖ + 1`，
  又 a.e. 强可测函数列的逐点极限仍 a.e. 强可测（`aestronglyMeasurable_of_tendsto_ae`），
  用控制函数得到可积性（`Integrable.mono'`）；
  (ii) 则直接调用区间积分的控制收敛定理
  `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`，
  控制函数取为 `‖f_N ·‖ + 2`（该定理的界只需对充分大的 `n` 成立，
  恰好省去对有限个 `n < N` 的处理）。
- 注意教材默认 `a ≤ b`；若 `b < a`，`[a, b] = ∅` 上的一致收敛是空泛成立的，
  结论并不成立，故形式化中必须显式假设 `hab : a ≤ b`。
-/
theorem tendstoUniformlyOn_Icc_intervalIntegrable
    {a b : ℝ} {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hab : a ≤ b)
    (hf : ∀ n, IntervalIntegrable (f n) volume a b)
    (h : TendstoUniformlyOn f F atTop (Icc a b)) :
    IntervalIntegrable F volume a b ∧
      Tendsto (fun n => ∫ x in a..b, f n x ∂volume) atTop
        (𝓝 (∫ x in a..b, F x ∂volume)) := by
  -- 一致收敛的 ε-N 刻画：∀ ε > 0, 最终 ∀ x ∈ [a,b], dist (F x) (f n x) < ε
  have hunif : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Icc a b, dist (F x) (f n x) < ε :=
    Metric.tendstoUniformlyOn_iff.mp h
  -- 取 ε = 1，得到一致控制指标 N
  have hev : ∀ᶠ n in atTop, ∀ x ∈ Icc a b, dist (F x) (f n x) < 1 :=
    hunif 1 one_pos
  obtain ⟨N, hN⟩ := hev.exists
  -- 一致收敛蕴含逐点收敛
  have hpt : ∀ x ∈ Icc a b, Tendsto (fun n => f n x) atTop (𝓝 (F x)) :=
    fun x hx => h.tendsto_at hx
  -- 由 a ≤ b 得 uIoc a b ⊆ Icc a b
  have hsub : uIoc a b ⊆ Icc a b := by
    rw [uIoc_of_le hab]
    exact Ioc_subset_Icc_self
  -- 每一项 f n 在 uIoc a b 上（关于限制测度）可积
  have hFn_int : ∀ n, Integrable (f n) (volume.restrict (uIoc a b)) :=
    fun n => intervalIntegrable_iff.mp (hf n)
  -- 控制函数 ‖f N ·‖ + c 的区间可积性
  have hbound_int : ∀ c : ℝ,
      IntervalIntegrable (fun x => ‖f N x‖ + c) volume a b := by
    intro c
    have h1 : IntervalIntegrable (fun x => ‖f N x‖) volume a b :=
      intervalIntegrable_iff.mpr (hFn_int N).norm
    have h2 : IntervalIntegrable (fun _ : ℝ => c) volume a b :=
      intervalIntegrable_const
    have h3 := h1.add h2
    simpa using h3
  -- (i) 先证极限函数 F 在 [a,b] 上可积
  have hF_int : IntervalIntegrable F volume a b := by
    -- F 是 a.e. 强可测函数列的逐点极限，故 a.e. 强可测
    have hmeas : AEStronglyMeasurable F (volume.restrict (uIoc a b)) := by
      have hall : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (uIoc a b)) :=
        fun n => (hFn_int n).aestronglyMeasurable
      have hae : ∀ᵐ x ∂(volume.restrict (uIoc a b)),
          Tendsto (fun n => f n x) atTop (𝓝 (F x)) := by
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
        exact hpt x (hsub hx)
      exact aestronglyMeasurable_of_tendsto_ae atTop hall hae
    -- 用控制函数 g(x) = ‖f N x‖ + 1 控制 F
    have hbound : Integrable (fun x => ‖f N x‖ + 1) (volume.restrict (uIoc a b)) :=
      intervalIntegrable_iff.mp (hbound_int 1)
    have hle : ∀ᵐ x ∂(volume.restrict (uIoc a b)),
        ‖F x‖ ≤ (fun x => ‖f N x‖ + 1) x := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
      have h1 : dist (F x) (f N x) < 1 := hN x (hsub hx)
      rw [dist_eq_norm] at h1
      have htri := norm_add_le (F x - f N x) (f N x)
      rw [sub_add_cancel] at htri
      show ‖F x‖ ≤ ‖f N x‖ + 1
      linarith
    have hF_integrable : Integrable F (volume.restrict (uIoc a b)) :=
      hbound.mono' hmeas hle
    exact intervalIntegrable_iff.mpr hF_integrable
  -- (ii) 积分与极限可交换：用区间积分的控制收敛定理，控制函数取 ‖f N ·‖ + 2
  have hlim : Tendsto (fun n => ∫ x in a..b, f n x ∂volume) atTop
      (𝓝 (∫ x in a..b, F x ∂volume)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖f N x‖ + 2) ?_ ?_ ?_ ?_
    · -- 每一项 a.e. 强可测
      exact Filter.Eventually.of_forall
        (fun n => (hFn_int n).aestronglyMeasurable)
    · -- 最终有一致界：n 充分大时，在 uIoc a b 上 ‖f n x‖ ≤ ‖f N x‖ + 2
      filter_upwards [hev] with n hn_close
      apply Filter.Eventually.of_forall
      intro x hx
      have hxIcc : x ∈ Icc a b := hsub hx
      have e1 : dist (F x) (f n x) < 1 := hn_close x hxIcc
      have e2 : dist (F x) (f N x) < 1 := hN x hxIcc
      rw [dist_eq_norm] at e1 e2
      have d1 : ‖f n x - F x‖ < 1 := by rwa [norm_sub_rev]
      have t1 := norm_add_le (f n x - F x) (F x)
      have t2 := norm_add_le (F x - f N x) (f N x)
      rw [sub_add_cancel] at t1 t2
      show ‖f n x‖ ≤ ‖f N x‖ + 2
      linarith
    · -- 控制函数区间可积
      exact hbound_int 2
    · -- 逐点收敛（a.e. 意义下）
      apply Filter.Eventually.of_forall
      intro x hx
      exact hpt x (hsub hx)
  exact ⟨hF_int, hlim⟩
