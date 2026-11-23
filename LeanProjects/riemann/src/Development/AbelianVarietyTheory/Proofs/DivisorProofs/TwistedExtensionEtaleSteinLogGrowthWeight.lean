import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffHoloSmoothDbarFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExtensionEtaleSteinSqIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoloLimitIncreasingWeightsStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.LogGrowth

noncomputable section

theorem db_const_fun {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : Fin n) (c : ℂ) :
    db n z k (fun _ => c) = fun _ => 0 := by
  funext x
  unfold db
  split_ifs <;> simp [wdb, Function.comp_def]

theorem d_const_fun {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (c : ℂ) (x : M) :
    d n z j (fun _ => c) x = 0 := by
  unfold d
  split_ifs <;> simp [wd, Function.comp_def]

theorem levi_const_fun {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℝ) (x : M)
    (ξ : Fin n → ℂ) : Levi n z (fun _ => c) x ξ = 0 := by
  simp only [Levi, db_const_fun, d_const_fun, zero_mul, Finset.sum_const_zero]

theorem ckR_two_of_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℝ)
    (h : SmoothR n z f) : CkR n z 2 f := fun e he => (h e he).of_le (by exact_mod_cast lse_two_le_infty)

theorem smoothR_const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℝ) :
    SmoothR n z (fun _ => c) := fun e _ => by
  simpa [Function.comp_def] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : V n => (c : ℂ)) e.target)

theorem levi_add_const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℝ) (c : ℝ)
    (hf : SmoothR n z f) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => f y + c) x ξ = Levi n z f x ξ := by
  have := levi_add n z f (fun _ => c) (ckR_two_of_smoothR n z f hf)
    (ckR_two_of_smoothR n z _ (smoothR_const n z c)) x ξ
  rw [this, levi_const_fun, add_zero]

theorem logShift_lse {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (X : EtaleStein n M) (k : ℕ) :
    SmoothR n X.z (fun x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1))) ∧
      LeviNonneg n X.z (fun x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1))) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hsub : SmoothR n X.z (fun y => X.e y + (-Real.log ((k : ℝ) + 1))) := by
    rw [lse_smoothR_iff_real]
    intro e he
    exact ((lse_smoothR_iff_real n X.z X.e).1 X.smooth_e e he).add contDiffOn_const
  have h := lse n M X.z X.isLocalHomeomorph 2 0
    ![fun _ => 0, fun y => X.e y + (-Real.log ((k : ℝ) + 1))] (fun j => j.elim0) ?_ ?_
    (fun j => j.elim0) ?_
  · have hfun : (fun x => Real.log (∑ i, Real.exp ((![fun _ => (0 : ℝ), fun y => X.e y + (-Real.log ((k : ℝ) + 1))] : Fin 2 → M → ℝ) i x) +
        ∑ j : Fin 0, ‖(j.elim0 : M → ℂ) x‖ ^ 2)) =
        fun x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1)) := by
      funext x
      simp [Fin.sum_univ_two, Real.exp_add, Real.exp_neg, Real.exp_log hk, div_eq_mul_inv]
    rw [hfun] at h
    exact h
  · intro i
    fin_cases i
    · exact smoothR_const n X.z 0
    · exact hsub
  · intro i
    fin_cases i
    · intro x ξ
      simp [levi_const_fun]
    · intro x ξ
      show 0 ≤ (Levi n X.z (fun y => X.e y + (-Real.log ((k : ℝ) + 1))) x ξ).re
      rw [levi_add_const n X.z X.e _ X.smooth_e]
      exact X.levi_e x ξ
  · intro x
    simp
    positivity

end

end GlobalTheory.LogGrowth

namespace GlobalTheory.LogGrowth

noncomputable section

theorem twisted_extension_logGrowth : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (φ ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ T : ℝ) (θ : ℝ → ℝ), SmoothR n X.z φ → SmoothR n X.z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → 300 ≤ T → IsCut T θ → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n X.z (fun x => φ x + α * ψ x)) → IsOpen Ω → Measurable G → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ -T + 1 → x ∈ Ω) → (∃ (N : ℕ) (C : ℝ), ∀ x, -ψ x ≤ N * X.e x + C) → wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) φ < ⊤ → ∃ F : M → ℂ, Holo n X.z F ∧ ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 * (wT T (δ * ψ x) * Real.exp (-(φ x + ψ x)))) ∂vol n X.z ≤ 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1}, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z := by
  intro n M _ _ _ _ _ X φ ψ G Ω δ T θ hφ hψ hψ0 hδ hT hθ hlevi hΩ hG hGhol hΩψ hgrow hfin
  obtain ⟨N, C, hNC⟩ := hgrow
  set B : ℝ≥0∞ := 30 * ∫⁻ x in {x | -T - 1 ≤ δ * ψ x ∧ δ * ψ x ≤ -T + 1},
    ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(φ x + ψ x))) ∂vol n X.z with hB
  by_cases hBtop : B = ⊤
  · refine ⟨fun _ => 0, fun e _ => differentiableOn_const 0, ?_⟩
    rw [hBtop]
    exact le_top
  have hBlt : B < ⊤ := lt_top_iff_ne_top.2 hBtop
  set Lk : ℕ → M → ℝ := fun k x => Real.log (1 + Real.exp (X.e x) / ((k : ℝ) + 1)) with hLk
  have hL : ∀ k, SmoothR n X.z (Lk k) ∧ LeviNonneg n X.z (Lk k) := fun k => logShift_lse X k
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL0 : ∀ k x, 0 ≤ Lk k x := by
    intro k x
    apply Real.log_nonneg
    have : 0 ≤ Real.exp (X.e x) / ((k : ℝ) + 1) := by positivity
    linarith
  have hLlow : ∀ (k : ℕ) (x : M), X.e x - Real.log ((k : ℝ) + 1) ≤ Lk k x := by
    intro k x
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have ha : 0 < Real.exp (X.e x) / ((k : ℝ) + 1) := by positivity
    calc X.e x - Real.log ((k : ℝ) + 1) = Real.log (Real.exp (X.e x) / ((k : ℝ) + 1)) := by
          rw [Real.log_div (Real.exp_pos _).ne' hk.ne', Real.log_exp]
      _ ≤ Lk k x := Real.log_le_log ha (by linarith)
  have hφR := (lse_smoothR_iff_real n X.z φ).1 hφ
  have hψR := (lse_smoothR_iff_real n X.z ψ).1 hψ
  have hsmk : ∀ k, SmoothR n X.z (fun x => φ x + N * Lk k x) := by
    intro k
    rw [lse_smoothR_iff_real]
    intro e he
    exact (hφR e he).add (contDiffOn_const.mul ((lse_smoothR_iff_real n X.z _).1 (hL k).1 e he))
  have hpk : ∀ k, SmoothR n X.z (fun x => (φ x + N * Lk k x) + ψ x) := by
    intro k
    rw [lse_smoothR_iff_real]
    intro e he
    exact ((lse_smoothR_iff_real n X.z _).1 (hsmk k) e he).add (hψR e he)
  have hstep : ∀ k : ℕ, ∃ F : M → ℂ, Holo n X.z F ∧
      ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x - F x‖ ^ 2 *
        (wT T (δ * ψ x) * Real.exp (-((φ x + N * Lk k x) + ψ x)))) ∂vol n X.z ≤ B := by
    intro k
    have hlev : ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ),
        LeviNonneg n X.z (fun x => (φ x + N * Lk k x) + α * ψ x) := by
      intro α hα x ξ
      have hfun : (fun x => (φ x + N * Lk k x) + α * ψ x) =
          fun y => (fun x => φ x + α * ψ x) y + (fun x => (N : ℝ) * Lk k x) y := by
        funext y; ring
      have hc1 : SmoothR n X.z (fun x => φ x + α * ψ x) := by
        rw [lse_smoothR_iff_real]
        intro e he
        exact (hφR e he).add (contDiffOn_const.mul (hψR e he))
      rw [hfun, levi_add n X.z (fun x => φ x + α * ψ x) (fun x => (N : ℝ) * Lk k x)
        (ckR_two_of_smoothR n X.z _ hc1)
        (ckR_two_of_smoothR n X.z _ (by
          rw [lse_smoothR_iff_real]
          intro e he
          exact contDiffOn_const.mul ((lse_smoothR_iff_real n X.z _).1 (hL k).1 e he))),
        levi_const_mul n X.z (N : ℝ) (Lk k) (ckR_two_of_smoothR n X.z _ (hL k).1)]
      rw [Complex.add_re, Complex.re_ofReal_mul]
      exact add_nonneg (hlevi α hα x ξ) (mul_nonneg hN0 ((hL k).2 x ξ))
    have hfin' : wint n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x)
        (fun x => (φ x + N * Lk k x) + ψ x) < ⊤ := by
      unfold wint at hfin ⊢
      have hK : ∀ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 *
          Real.exp (-((φ x + N * Lk k x) + ψ x))) ≤
          ENNReal.ofReal (Real.exp (C + N * Real.log ((k : ℝ) + 1))) *
            ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-φ x)) := by
        intro x
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        have h2 : (N : ℝ) * X.e x - N * Real.log ((k : ℝ) + 1) ≤ N * Lk k x := by
          have := mul_le_mul_of_nonneg_left (hLlow k x) hN0
          linarith [mul_sub (N : ℝ) (X.e x) (Real.log ((k : ℝ) + 1))]
        have h3 : Real.exp (-((φ x + N * Lk k x) + ψ x)) ≤
            Real.exp (C + N * Real.log ((k : ℝ) + 1)) * Real.exp (-φ x) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          linarith [hNC x]
        calc ‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-((φ x + N * Lk k x) + ψ x))
            ≤ ‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 *
              (Real.exp (C + N * Real.log ((k : ℝ) + 1)) * Real.exp (-φ x)) :=
              mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
          _ = _ := by ring
      calc _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (C + N * Real.log ((k : ℝ) + 1))) *
            ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-φ x)) ∂vol n X.z :=
            lintegral_mono hK
        _ = ENNReal.ofReal (Real.exp (C + N * Real.log ((k : ℝ) + 1))) *
            ∫⁻ x, ENNReal.ofReal (‖(θ (δ * ψ x) : ℂ) * G x‖ ^ 2 * Real.exp (-φ x)) ∂vol n X.z :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
    obtain ⟨F, hF, hFle⟩ := GlobalTheory.T.twistedExtension_etaleStein_sqIntegrable n M X (fun x => φ x + N * Lk k x) ψ G Ω δ T θ (hsmk k)
      hψ hψ0 hδ hT hθ hlev hΩ hG hGhol hΩψ hfin'
    refine ⟨F, hF, hFle.trans ?_⟩
    rw [hB]
    refine mul_le_mul_of_nonneg_left (lintegral_mono fun x => ?_) (zero_le)
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.2
    have := mul_nonneg hN0 (hL0 k x)
    linarith
  choose F hFholo hFle using hstep
  have hz := X.isLocalHomeomorph
  have hψc : Continuous ψ := by
    have h := Smooth.continuous n X.z hz _ hψ
    simpa [Function.comp_def] using Complex.continuous_re.comp h
  have hF0 := (GlobalTheory.T.cutoff_holo_smooth_dbar_formula n M X ψ G Ω δ (-T + 1) θ hψ hθ.1 hθ.2.2.1 hΩ hGhol hΩψ).1
  have hF0c := Smooth.continuous n X.z hz _ hF0
  have hden : ∀ x, 0 < 1 + min ((δ * ψ x) ^ 2) ((T + 1) ^ 2) := fun x =>
    add_pos_of_pos_of_nonneg one_pos (le_min (sq_nonneg _) (sq_nonneg _))
  have homc : Continuous (fun x => wT T (δ * ψ x)) := by
    unfold wT
    exact Continuous.div continuous_const (continuous_const.add
      (((continuous_const.mul hψc).pow 2).min continuous_const)) fun x => (hden x).ne'
  have hc : (0 : ℝ) < 1 / (1 + (T + 1) ^ 2) := by positivity
  have hbd : ∀ x, 1 / (1 + (T + 1) ^ 2) ≤ wT T (δ * ψ x) ∧ wT T (δ * ψ x) ≤ 1 := by
    intro x
    unfold wT
    constructor
    · exact one_div_le_one_div_of_le (hden x) (by linarith [min_le_right ((δ * ψ x) ^ 2) ((T + 1) ^ 2)])
    · rw [div_le_one (hden x)]
      linarith [le_min (sq_nonneg (δ * ψ x)) (sq_nonneg (T + 1))]
  have hanti : ∀ x, Antitone (fun k => (φ x + N * Lk k x) + ψ x) := by
    intro x k k' hkk
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hkk' : (k : ℝ) + 1 ≤ (k' : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkk 1
    have h1 : Lk k' x ≤ Lk k x := by
      apply Real.log_le_log (by have : 0 ≤ Real.exp (X.e x) / ((k' : ℝ) + 1) := by positivity
                                linarith)
      have := div_le_div_of_nonneg_left (Real.exp_pos (X.e x)).le hk hkk'
      linarith
    have := mul_le_mul_of_nonneg_left h1 hN0
    show (φ x + N * Lk k' x) + ψ x ≤ (φ x + N * Lk k x) + ψ x
    linarith
  have htend : ∀ x, Tendsto (fun k => (φ x + N * Lk k x) + ψ x) atTop (𝓝 (φ x + ψ x)) := by
    intro x
    have h1 : Tendsto (fun k : ℕ => Real.exp (X.e x) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      have h2 := (tendsto_const_div_atTop_nhds_zero_nat (Real.exp (X.e x))).comp
        (tendsto_add_atTop_nat 1)
      refine h2.congr fun k => ?_
      simp [Function.comp]
    have h3 : Tendsto (fun k : ℕ => Lk k x) atTop (𝓝 (Real.log (1 + 0))) :=
      ((Real.continuousAt_log (by norm_num)).tendsto).comp (tendsto_const_nhds.add h1)
    rw [add_zero, Real.log_one] at h3
    have h4 := ((tendsto_const_nhds (x := φ x)).add (h3.const_mul (N : ℝ))).add_const (ψ x)
    simpa using h4
  obtain ⟨Gf, hGf, hGle⟩ := GlobalTheory.T.exists_holo_l2_bound_of_increasing_weights n M X (fun x => (θ (δ * ψ x) : ℂ) * G x)
    (fun x => wT T (δ * ψ x)) (1 / (1 + (T + 1) ^ 2)) (fun k x => (φ x + N * Lk k x) + ψ x)
    (fun x => φ x + ψ x) F B hF0c homc hc hbd hpk hanti htend hFholo hBlt hFle
  exact ⟨Gf, hGf, hGle⟩

end

end GlobalTheory.LogGrowth
