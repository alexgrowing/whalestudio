import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockModelPosFrameBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricBoundPuncturedPolydisc
import Development.AutomorphicArithmetic.DivisorFrames.PoincareDerivativeBound
open Matrix Filter Topology
open scoped ComplexOrder

open GlobalTheory.HermFrame in
private theorem norm_le_gnorm_one' {g : ℕ} (v : Fin g → ℂ) : ‖v‖ ≤ gnorm 1 v := by
  rw [GlobalTheory.ConnPointwise.gnorm_one_eq]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun k => Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun a => ‖v a‖ ^ 2) (fun l _ => by positivity) (Finset.mem_univ k)

open GlobalTheory.HermFrame in
private theorem gnorm_one_le' {g : ℕ} (v : Fin g → ℂ) : gnorm 1 v ≤ g * ‖v‖ := by
  rw [GlobalTheory.ConnPointwise.gnorm_one_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc ∑ a, ‖v a‖ ^ 2 ≤ ∑ _a : Fin g, ‖v‖ ^ 2 :=
        Finset.sum_le_sum fun a _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v a) 2
    _ = g * ‖v‖ ^ 2 := by simp
    _ ≤ (g * ‖v‖) ^ 2 := by
        rw [mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast Nat.le_self_pow two_ne_zero g

open GlobalTheory.HermFrame in
private theorem gnorm_scaled' {g : ℕ} {d : ℝ} (hd : 0 < d) (v : Fin g → ℂ) :
    gnorm ((((d⁻¹ ^ 2 : ℝ)) : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) v = d⁻¹ * gnorm 1 v := by
  rw [gnorm, gnorm, form_smul, Complex.re_ofReal_mul, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]

open GlobalTheory.HermFrame GlobalTheory.CurvInterp GlobalTheory.CurvInterp.Block GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram in
theorem UpperTheory.curvature_connection_bound :
    ∀ (e : ℕ) (ι : Type) [Fintype ι] (μ : ι → ℕ) (ρ : ℝ) (U : Set (Fin e → ℂ)) (H : ∀ τ, (Fin e → ℂ) → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ) (δ : (Fin e → ℂ) → ℝ), 0 < ρ → GlobalTheory.CurvInterp.IsBlockModel ρ U H → (∀ᶠ z in 𝓝 (0 : Fin e → ℂ), z ∈ U → 0 < δ z ∧ δ z ≤ 1 ∧ Metric.ball z (δ z) ⊆ U) → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z in 𝓝 (0 : Fin e → ℂ), z ∈ U → ∀ (τ : ι) (ξ : Fin e → ℂ) (v : Fin (μ τ) → ℂ), ‖GlobalTheory.HermFrame.conn (H τ) z ξ *ᵥ v‖ ≤ C / δ z * ‖ξ‖ * ‖v‖ := by
  intro e ι _ μ ρ U H δ hρ ⟨n, k, hk, g, rk, τ₀, B, φ, Q, κ, hP, hφ, hφ0, hφ1, hQ, hcard, hli, hκ, hH⟩ hδ
  classical
  obtain ⟨ρ₁, c₀, C, hρ₁, hρ₁', -, -, -, h1, h2⟩ := GlobalTheory.HodgeChartRow.hodgeChartBounds_of_schur_lemW
    GlobalTheory.schur_block_lower_bound GlobalTheory.smul_inv_mul_posSemidef_uniform_bound n k g rk hk τ₀ B hP
  let ε : (Σ τ, Fin (μ τ)) ≃ Fin g := Fintype.equivFinOfCardEq hcard
  let A : (Fin e → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun z => of fun l i => Q (ε.symm i).1 z (ε.symm i).2 l
  have hA : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, ∀ i l, AnalyticAt ℂ (fun x => A x i l) z := fun z hz i l =>
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball (hQ _ _ _) z hz
  have hφa := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn Metric.isOpen_ball hφ
  have hA0 : IsUnit (A 0).det := by
    rw [← det_transpose, ← isUnit_iff_isUnit_det, ← linearIndependent_rows_iff_isUnit]
    exact hli.comp ε.symm ε.symm.injective
  obtain ⟨b, hb0, hb⟩ := holo_local_bounds (hA 0 (Metric.mem_ball_self hρ)) hA0
  have hnear : ∀ᶠ z in 𝓝 (0 : Fin e → ℂ), ‖φ z‖ < ρ₁ :=
    (hφa 0 (Metric.mem_ball_self hρ)).continuousAt.norm.eventually_lt continuousAt_const (by simpa [hφ0] using hρ₁)
  obtain ⟨ρ₃, hρ₃, h3⟩ := Metric.eventually_nhds_iff_ball.1 ((hb.and hnear).and hδ)
  set ρ' := min (ρ / 2) ρ₃ with hρ'
  have l2 : ρ' ≤ ρ / 2 := min_le_left _ _
  have l3 : ρ' ≤ ρ₃ := min_le_right _ _
  have l0 : ρ' ≤ ρ := by linarith
  have hρ'0 : 0 < ρ' := lt_min (by positivity) hρ₃
  set V : Set (Fin e → ℂ) := Metric.ball 0 ρ' ∩ U with hVdef
  let G : (Fin e → ℂ) → Matrix (Fin e) (Fin e) ℂ := fun z => ((((δ z)⁻¹ ^ 2 : ℝ)) : ℂ) • 1
  have hV : ∀ z ∈ V, z ∈ Metric.ball (0 : Fin e → ℂ) ρ ∧ z ∈ U := fun z hz =>
    ⟨Metric.ball_subset_ball l0 hz.1, hz.2⟩
  have h3' := fun z (hz : z ∈ V) => (h3 z (Metric.ball_subset_ball l3 hz.1)).1
  have hd := fun z (hz : z ∈ V) => (h3 z (Metric.ball_subset_ball l3 hz.1)).2 hz.2
  have hVo : IsOpen V := isOpen_iff_mem_nhds.2 fun z hz =>
    inter_mem (Metric.isOpen_ball.mem_nhds hz.1) (mem_of_superset (Metric.ball_mem_nhds z (hd z hz).1) (hd z hz).2.2)
  have hG : ∀ z ∈ V, (G z).PosSemidef := fun z hz =>
    PosSemidef.one.smul (by rw [Complex.zero_le_real]; positivity)
  have hGn : ∀ z ∈ V, ∀ w, gnorm (G z) w = (δ z)⁻¹ * gnorm 1 w := fun z hz w => gnorm_scaled' (hd z hz).1 w
  have hH' := fun z (hz : z ∈ V) => hH z (hV z hz).1 (hV z hz).2
  set m := min 1 (ρ / 2) with hm
  have hm0 : 0 < m := lt_min one_pos (by positivity)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hm2 : m ≤ ρ / 2 := min_le_right _ _
  set D : ℝ := ((n : ℝ) + 1) * (8 * Real.pi) / m with hD
  have hD0 : 0 ≤ D := by positivity
  have hS : ∀ z ∈ V, ∀ w, gnorm (poincareGram k (φ z)) (fderiv ℂ φ z w) ≤ D * gnorm (G z) w := fun z hz w => by
    obtain ⟨d0, d1, d2⟩ := hd z hz
    have s1 : Metric.ball z (δ z * m) ⊆ Metric.ball 0 ρ := Metric.ball_subset_ball' (by
      have := Metric.mem_ball.1 hz.1
      nlinarith)
    have s2 : Metric.ball z (δ z * m) ⊆ U := (Metric.ball_subset_ball (by nlinarith)).trans d2
    refine (UpperTheory.poincare_derivative_bound e n k hk φ z (δ z * m) (by positivity) (hφ.mono s1)
      (fun x hx => (hH x (s1 hx) (s2 hx)).1) w).trans ?_
    rw [hGn z hz]
    calc ((n : ℝ) + 1) * (8 * Real.pi) * (‖w‖ / (δ z * m)) = D * ((δ z)⁻¹ * ‖w‖) := by
          rw [hD]; field_simp
      _ ≤ D * ((δ z)⁻¹ * gnorm 1 w) := by gcongr; exact norm_le_gnorm_one' w
  obtain ⟨p0, p1, p2⟩ := bounds_pullback (V := V) (G := G) (φ := φ) (le_max_right C 0)
    (le_max_right D 1) hVo hG
    (fun w hw => (GlobalTheory.HodgeGramLocal.hodgeGram_local n k g rk hk τ₀ B hP w
      ⟨fun i => (hw.1 i).trans_le (hρ₁'.trans (by norm_num)), hw.2⟩).1)
    (h1.mono (le_max_left _ _)) (h2.mono (le_max_left _ _)) (fun z hz => hφa z (hV z hz).1)
    (fun z hz => ⟨fun i => (norm_le_pi_norm _ i).trans_lt (h3' z hz).2, (hH' z hz).1.2⟩)
    fun z hz w => (hS z hz w).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (gnorm_nonneg _ _))
  obtain ⟨q0, q1, q2⟩ := bounds_dual_changeFrame (A := A) (by positivity) hb0 p0 p1 p2
    (fun z hz => hA z (hV z hz).1) fun z hz => by
      obtain ⟨⟨a1, a2, a3, a4⟩, -⟩ := h3' z hz
      refine ⟨a1, a2, a3, fun ξ => (a4 ξ).trans (mul_le_mul_of_nonneg_left ?_ hb0)⟩
      rw [hGn z hz]
      exact (norm_le_gnorm_one' ξ).trans
        (le_mul_of_one_le_left (gnorm_nonneg _ _) ((one_le_inv₀ (hd z hz).1).2 (hd z hz).2.1))
  have hent : ∀ z ∈ V, ∀ (p p' : Σ τ, Fin (μ τ)),
      ((A z)ᵀ * dualGram (hodgeGram hk τ₀ B (φ z)) * (A z)ᴴᵀ) (ε p) (ε p') =
        (Q p.1 z * (hodgeGram hk τ₀ B (φ z))⁻¹ * (Q p'.1 z)ᴴ) p.2 p'.2 := fun z hz p p' => by
    have hs : (hodgeGram hk τ₀ B (φ z)).IsSymm := IsSymm.ext fun a c => by
      have hB : ∀ i, (B i c a : ℝ) = B i a c := fun i => by simpa using (hP.psd i).isHermitian.apply a c
      simp [hodgeGram, imPeriod, Matrix.sum_apply, hB, (hP.symm _ (hH' z hz).1.1).apply]
    rw [dualGram, transpose_nonsing_inv, hs.eq]
    simp only [mul_apply, transpose_apply, conjTranspose_apply, A, of_apply]
    rw [ε.symm_apply_apply, ε.symm_apply_apply]
  set C₁ : ℝ := b * (max C 0 * max D 1 ^ 2 * b + b) with hC₁
  set C₂ : ℝ := max C₁ (max C 0 * max D 1 ^ 2) with hC₂
  have hC₂0 : 0 ≤ C₂ := le_max_of_le_right (by positivity)
  have key : ∀ τ, OneFormBound V (fun _ => (1 : Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ)) G (conn (H τ)) C₂ := fun τ => by
    refine (bounds_block (H := H τ) (j := fun a => ε ⟨τ, a⟩) (hκ τ)
      (ε.injective.comp sigma_mk_injective) q0 (q1.mono (le_max_left _ _)) (q2.mono (le_max_right _ _))
      (fun z hz s a hs => ?_) fun z hz => ?_).2.1
    · obtain ⟨⟨τ', a'⟩, rfl⟩ := ε.surjective s
      have hne : τ' ≠ τ := by rintro rfl; exact hs ⟨a', rfl⟩
      rw [hent z hz, (hH' z hz).2.2 τ' τ hne, Matrix.zero_apply]
    · rw [(hH' z hz).2.1 τ]
      congr 1
      ext a a'
      exact (hent z hz ⟨τ, a⟩ ⟨τ, a'⟩).symm
  refine ⟨C₂ * e * ∑ τ, (μ τ : ℝ), by positivity, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : Fin e → ℂ) hρ'0] with z hz hU τ ξ v
  have hzV : z ∈ V := ⟨hz, hU⟩
  have d0 := (hd z hzV).1
  have k1 := (key τ z hzV).2.2 ξ
  rw [hGn z hzV] at k1
  have k2 : (μ τ : ℝ) ≤ ∑ τ, (μ τ : ℝ) :=
    Finset.single_le_sum (f := fun τ => (μ τ : ℝ)) (fun _ _ => by positivity) (Finset.mem_univ τ)
  calc ‖conn (H τ) z ξ *ᵥ v‖ ≤ gnorm 1 (conn (H τ) z ξ *ᵥ v) := norm_le_gnorm_one' _
    _ ≤ opNorm 1 1 (conn (H τ) z ξ) * gnorm 1 v := gnorm_mulVec_le PosDef.one PosSemidef.one _ _
    _ ≤ (C₂ * ((δ z)⁻¹ * (e * ‖ξ‖))) * ((∑ τ, (μ τ : ℝ)) * ‖v‖) := by
        refine mul_le_mul (k1.trans ?_) ((gnorm_one_le' v).trans ?_) (gnorm_nonneg _ _) (by positivity)
        · gcongr; exact gnorm_one_le' ξ
        · gcongr
    _ = (C₂ * e * ∑ τ, (μ τ : ℝ)) / δ z * ‖ξ‖ * ‖v‖ := by rw [div_eq_mul_inv]; ring
