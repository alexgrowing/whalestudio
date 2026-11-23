import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarCompactLtTop
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevInequalityAtIdentityBesselModelUnitaryGroStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoAverageL2CompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BallMeanContinuousLinearFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothFunctionalOrbitSmoothVectorStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevIneqTranslateCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousLimitUniformCauchyStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem sq_nnnorm_sub_le {W : Type} [NormedAddCommGroup W] (a b c : W) :
    (‖a - b‖₊ : ENNReal) ^ 2 ≤ 2 * (‖a - c‖₊ : ENNReal) ^ 2 + 2 * (‖b - c‖₊ : ENNReal) ^ 2 := by
  have h : ‖a - b‖ ≤ ‖a - c‖ + ‖b - c‖ := by
    simpa [norm_sub_rev] using norm_sub_le_norm_sub_add_norm_sub a c b
  have h2 : (‖a - b‖₊ : NNReal) ^ 2 ≤ 2 * (‖a - c‖₊ : NNReal) ^ 2 + 2 * (‖b - c‖₊ : NNReal) ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [sq_nonneg (‖a - c‖ - ‖b - c‖), norm_nonneg (a - b), norm_nonneg (a - c),
      norm_nonneg (b - c)]
  exact_mod_cast h2

theorem list_sq_le {ι : Type} (c : ℝ) (hc : 0 ≤ c) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (l : List ι) :
    (l.map fun w => 2 * ENNReal.ofReal (c * a w ^ 2)).sum ≤
      ENNReal.ofReal (2 * c * (l.map a).sum ^ 2) := by
  induction l with
  | nil => simp
  | cons w l ih =>
    have hS : 0 ≤ (l.map a).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact ha i)
    simp only [List.map_cons, List.sum_cons]
    have e : 2 * ENNReal.ofReal (c * a w ^ 2) = ENNReal.ofReal (2 * (c * a w ^ 2)) := by
      rw [ENNReal.ofReal_mul (p := 2) (q := c * a w ^ 2) (by norm_num)]; simp
    rw [e]
    refine (add_le_add le_rfl ih).trans ?_
    rw [← ENNReal.ofReal_add (by have := ha w; positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := ha w
    nlinarith [mul_nonneg hc (mul_nonneg this hS)]

theorem list_sum_le_two {ι : Type} (l : List ι) (A a b : ι → ENNReal)
    (h : ∀ i ∈ l, A i ≤ 2 * a i + 2 * b i) :
    (l.map A).sum ≤ 2 * (l.map a).sum + 2 * (l.map b).sum := by
  induction l with
  | nil => simp
  | cons w l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    have h1 := h w List.mem_cons_self
    have h2 := ih fun i hi => h i (List.mem_cons_of_mem _ hi)
    calc A w + (l.map A).sum ≤ (2 * a w + 2 * b w) + (2 * (l.map a).sum + 2 * (l.map b).sum) :=
          add_le_add h1 h2
      _ = 2 * a w + 2 * (l.map a).sum + (2 * b w + 2 * (l.map b).sum) := by
          rw [add_add_add_comm]

theorem reg_main : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (T : H → Mat k r → Wp), IsURepOn (GG k r) σ → IsHaarOn (GG k r) μG → (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x) + T u' (Matrix.of x)) → (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) → (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) → (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x * y)) → ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧ ∀ u : H, IsSmoothVec σ u → ∃ f : Mat k r → Wp, ContinuousOn f (GG k r) ∧ (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] (fun x => T u (Matrix.of x)) ∧ ‖f 1‖ ≤ C * (Ws.map fun ws => ‖dsigW σ ws u‖).sum := by
  intro k r H _ _ _ Wp _ _ _ σ μ T hσ hμ hadd hsm hbd heq
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hGae : ∀ᵐ y ∂μ, (Matrix.of y : Mat k r) ∈ GG k r := by
    rw [ae_iff]; exact hμ.2.2.1
  have hGm : MeasurableSet {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} :=
    IsClosed.measurableSet (α := Mt k r) (gg_closedSub k r).2.1
  have hrest : μ.restrict {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} = μ :=
    Measure.restrict_eq_self_of_ae_mem hGae
  have hcm : ∀ (Λ' : H →L[ℂ] Wp) (v : H),
      AEStronglyMeasurable (fun y : Mt k r => Λ' (σ (Matrix.of y) v)) μ := by
    intro Λ' v
    have hc : ContinuousOn (fun y : Mt k r => Λ' (σ (Matrix.of y) v))
        {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} :=
      Λ'.continuous.comp_continuousOn (hσ.2.2 v)
    have := hc.aestronglyMeasurable (μ := μ) hGm
    rwa [hrest] at this
  obtain ⟨C₀, Ws, K₀, hK₀, hWs, hsob⟩ := GlobalTheory.T.sobolev_inequality_at_identity_besselModelUnitaryGroup k r μ hμ
  have hsu := GlobalTheory.T.sobolev_ineq_translate_compact k r μ C₀ Ws K₀ hμ hK₀ hsob
  have hclm : ∀ Q : Set (Mt k r), IsCompact Q → ∃ K₂ : Set (Mt k r), IsCompact K₂ ∧
      ∀ (Λ' : H →L[ℂ] Wp) (u : H), IsSmoothVec (k := k) (r := r) σ u → ∀ x ∈ Q,
      (Matrix.of x : Mat k r) ∈ GG k r →
      ENNReal.ofReal (‖Λ' (σ (Matrix.of x) u)‖ ^ 2) ≤ ENNReal.ofReal |C₀| *
        (Ws.map fun ws => ∫⁻ y in K₂, (‖Λ' (σ (Matrix.of y) (dsigW σ ws u))‖₊ : ENNReal) ^ 2 ∂μ).sum := by
    intro Q hQ
    obtain ⟨K₂, hK₂, h⟩ := hsu Q hQ
    refine ⟨K₂, hK₂, fun Λ' u hu x hx hxG => ?_⟩
    obtain ⟨hs, hd⟩ := GlobalTheory.T.smooth_functional_orbit_smoothVector k r σ Λ' hσ u hu
    have hcont : ∀ ws ∈ Ws, ContinuousOn (rdWord ws fun g : Mat k r => Λ' (σ g u)) (GG k r) := by
      intro ws hws
      have h1 : ContinuousOn (fun g : Mat k r => Λ' (σ g (dsigW σ ws u))) (GG k r) :=
        Λ'.continuous.comp_continuousOn (hσ.2.2 _)
      exact h1.congr (fun x hx => hd ws (hWs ws hws) x hx)
    refine (h Wp _ hs hcont x hx hxG).trans (le_of_eq ?_)
    congr 2
    refine List.map_congr_left fun ws hws => ?_
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hGae] with y hy
    rw [hd ws (hWs ws hws) _ hy]
  obtain ⟨K₁, hK₁, hone⟩ := hclm {oneM k r} isCompact_singleton
  obtain ⟨c₁, hc₁⟩ := hbd K₁ hK₁
  choose Λ hΛ using GlobalTheory.T.ballMean_continuousLinearFunctional k r σ μ T hμ hadd hsm hbd heq
  refine ⟨Real.sqrt (|C₀| * (2 * |c₁|)), Ws, hWs, fun u hu => ?_⟩
  have hloc : ∀ (v : H) (K : Set (Mt k r)), IsCompact K →
      AEStronglyMeasurable (fun z : Mt k r => T v (Matrix.of z)) (μ.restrict K) ∧
      ∫⁻ x in K, (‖T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ < ⊤ := by
    intro v K hK
    obtain ⟨C, hC⟩ := hbd K hK
    exact ⟨(hC v).1, (hC v).2.trans_lt ENNReal.ofReal_lt_top⟩
  have hconv : ∀ (v : H) (K : Set (Mt k r)), IsCompact K → Filter.Tendsto (fun j : ℕ =>
      ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ)
      Filter.atTop (nhds 0) :=
    fun v K hK => GlobalTheory.T.tendsto_average_L2_compact k r μ hμ _ (hloc v) K hK

  have hAm : ∀ (j : ℕ) (v : H) (K : Set (Mt k r)), IsCompact K → AEMeasurable (fun y : Mt k r =>
      (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) y - T v (Matrix.of y)‖₊ : ENNReal) ^ 2) (μ.restrict K) := by
    intro j v K hK
    have h1 : AEStronglyMeasurable (fun y : Mt k r => avgR μ j (fun z : Mt k r => T v (Matrix.of z)) y) μ := by
      refine (hcm (Λ j) v).congr ?_
      filter_upwards [hGae] with x hx
      exact hΛ j v x hx
    exact ((h1.restrict.sub (hloc v K hK).1).nnnorm.aemeasurable.coe_nnreal_ennreal).pow_const 2

  have hsp : ∀ (j l : ℕ) (v : H) (K : Set (Mt k r)), IsCompact K →
      ∫⁻ y in K, (‖(Λ j - Λ l) (σ (Matrix.of y) v)‖₊ : ENNReal) ^ 2 ∂μ ≤
      2 * ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ +
      2 * ∫⁻ x in K, (‖avgR μ l (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ := by
    intro j l v K hK
    rw [← lintegral_const_mul' 2 _ (by simp), ← lintegral_const_mul' 2 _ (by simp),
      ← lintegral_add_left' ((hAm j v K hK).const_mul 2)]
    refine lintegral_mono_ae (ae_restrict_of_ae ?_)
    filter_upwards [hGae] with y hy
    rw [ContinuousLinearMap.sub_apply, hΛ j v y hy, hΛ l v y hy]
    exact sq_nnnorm_sub_le _ _ _
  have hsp1 : ∀ (j : ℕ) (v : H) (K : Set (Mt k r)), IsCompact K →
      ∫⁻ y in K, (‖Λ j (σ (Matrix.of y) v)‖₊ : ENNReal) ^ 2 ∂μ ≤
      2 * ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T v (Matrix.of z)) x - T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ +
      2 * ∫⁻ x in K, (‖T v (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ := by
    intro j v K hK
    rw [← lintegral_const_mul' 2 _ (by simp), ← lintegral_const_mul' 2 _ (by simp),
      ← lintegral_add_left' ((hAm j v K hK).const_mul 2)]
    refine lintegral_mono_ae (ae_restrict_of_ae ?_)
    filter_upwards [hGae] with y hy
    rw [hΛ j v y hy]
    simpa using sq_nnnorm_sub_le (avgR μ j (fun z : Mt k r => T v (Matrix.of z)) y) 0 (T v (Matrix.of y))
  have hEt : ∀ K : Set (Mt k r), IsCompact K → Filter.Tendsto (fun j : ℕ =>
      (Ws.map fun ws => ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
        T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ).sum) Filter.atTop (nhds 0) := by
    intro K hK
    have h := tendsto_list_sum (f := fun (ws : List (Mat k r)) (j : ℕ) =>
      ∫⁻ x in K, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
        T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ) (a := fun _ => 0) Ws
      (fun ws _ => hconv _ K hK)
    have e0 : (Ws.map fun _ => (0 : ENNReal)).sum = 0 := by simp
    rwa [e0] at h
  have hCau : ∀ Q : Set (Mt k r), IsCompact Q → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ N, ∀ x ∈ Q,
      (Matrix.of x : Mat k r) ∈ GG k r →
      ‖Λ j (σ (Matrix.of x) u) - Λ l (σ (Matrix.of x) u)‖ ≤ ε := by
    intro Q hQ ε hε
    obtain ⟨K₂, hK₂, h⟩ := hclm Q hQ
    have hG : Filter.Tendsto (fun j : ℕ => ENNReal.ofReal |C₀| * (2 *
        (Ws.map fun ws => ∫⁻ x in K₂, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
          T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ).sum)) Filter.atTop (nhds 0) := by
      have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |C₀|)
        (ENNReal.Tendsto.const_mul (a := 2) (hEt K₂ hK₂) (Or.inr (by simp)))
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h1
    have hη : (0 : ENNReal) < ENNReal.ofReal (ε ^ 2 / 2) := ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hG.eventually_lt_const hη)
    refine ⟨N, fun j hj l hl x hx hxG => ?_⟩
    have hb := h (Λ j - Λ l) u hu x hx hxG
    have hs := list_sum_le_two Ws _ _ _ (fun ws _ => hsp j l (dsigW σ ws u) K₂ hK₂)
    have h3 : ENNReal.ofReal (‖(Λ j - Λ l) (σ (Matrix.of x) u)‖ ^ 2) ≤
        ENNReal.ofReal (ε ^ 2 / 2) + ENNReal.ofReal (ε ^ 2 / 2) := by
      refine hb.trans ((mul_le_mul' le_rfl hs).trans ?_)
      rw [mul_add]
      exact add_le_add (hN j hj).le (hN l hl).le
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
    have h4 : ‖(Λ j - Λ l) (σ (Matrix.of x) u)‖ ^ 2 ≤ ε ^ 2 := by linarith
    have h5 := (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le (by norm_num)).1 h4
    simpa using h5
  obtain ⟨F, hFc, hFae, hFl⟩ := GlobalTheory.T.exists_continuous_limit_uniformCauchy k r μ hμ (fun j g => Λ j (σ g u))
    (fun z : Mt k r => T u (Matrix.of z)) (fun j => (Λ j).continuous.comp_continuousOn (hσ.2.2 u))
    (fun Q hQ => (hloc u Q hQ).1) hCau (fun Q hQ => by
      refine (hconv u Q hQ).congr fun j => ?_
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hGae] with x hx
      rw [hΛ j u x hx])
  refine ⟨F, hFc, hFae, ?_⟩
  have h1G : (1 : Mat k r) ∈ GG k r := (gg_closedSub k r).2.2.1
  have hlim := hFl 1 h1G
  have hb : ∀ j : ℕ, ENNReal.ofReal (‖Λ j (σ 1 u)‖ ^ 2) ≤ ENNReal.ofReal |C₀| * (2 *
      (Ws.map fun ws => ∫⁻ x in K₁, (‖avgR μ j (fun z : Mt k r => T (dsigW σ ws u) (Matrix.of z)) x -
          T (dsigW σ ws u) (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μ).sum +
      2 * (Ws.map fun ws => ENNReal.ofReal (|c₁| * ‖dsigW σ ws u‖ ^ 2)).sum) := by
    intro j
    have h0 := hone (Λ j) u hu (oneM k r) rfl h1G
    refine h0.trans (mul_le_mul' le_rfl (list_sum_le_two Ws _ _ _ fun ws _ => ?_))
    refine (hsp1 j (dsigW σ ws u) K₁ hK₁).trans ?_
    gcongr
    refine (hc₁ _).2.trans (ENNReal.ofReal_le_ofReal ?_)
    have := le_abs_self c₁
    have h2 := sq_nonneg ‖dsigW σ ws u‖
    nlinarith
  have hlimL : Filter.Tendsto (fun j : ℕ => ENNReal.ofReal (‖Λ j (σ 1 u)‖ ^ 2)) Filter.atTop
      (nhds (ENNReal.ofReal (‖F 1‖ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hlim.norm.pow 2)
  have hlimR := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |C₀|)
    ((ENNReal.Tendsto.const_mul (a := 2) (hEt K₁ hK₁) (Or.inr (by simp))).add
      (tendsto_const_nhds (x := 2 * (Ws.map fun ws => ENNReal.ofReal (|c₁| * ‖dsigW σ ws u‖ ^ 2)).sum)))
    (Or.inr ENNReal.ofReal_ne_top)
  have hfin := le_of_tendsto_of_tendsto' hlimL hlimR hb
  rw [mul_zero, zero_add, ← List.sum_map_mul_left] at hfin
  have hS := list_sq_le |c₁| (abs_nonneg _) (fun ws : List (Mat k r) => ‖dsigW σ ws u‖)
    (fun _ => norm_nonneg _) Ws
  have hSn : 0 ≤ (Ws.map fun ws => ‖dsigW σ ws u‖).sum := List.sum_nonneg (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _)
  have h3 := hfin.trans (mul_le_mul' le_rfl hS)
  rw [← ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  have h4 := Real.abs_le_sqrt (h := h3)
  rw [abs_norm] at h4
  have e : |C₀| * (2 * |c₁| * (Ws.map fun ws => ‖dsigW σ ws u‖).sum ^ 2) =
      (|C₀| * (2 * |c₁|)) * (Ws.map fun ws => ‖dsigW σ ws u‖).sum ^ 2 := by ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hSn] at h4
  exact h4

end GlobalTheory.SgInf
