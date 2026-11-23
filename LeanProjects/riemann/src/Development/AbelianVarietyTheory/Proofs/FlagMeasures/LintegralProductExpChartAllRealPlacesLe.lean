import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyBallSubset

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.ProductChartAll

open scoped ENNReal in

theorem le_smul_pi {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
    (ν : Measure (∀ i, α i)) (μ : ∀ i, Measure (α i)) {K : ℝ≥0∞} (h0 : K ≠ 0) (h1 : K ≠ ⊤)
    (h : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) →
      ν (Set.pi Set.univ s) ≤ K * ∏ i, μ i (s i)) :
    ν ≤ K • Measure.pi μ := by

  have hout : K⁻¹ • ν.toOuterMeasure ≤ OuterMeasure.pi fun i => (μ i).toOuterMeasure := by
    refine OuterMeasure.le_pi.2 fun s _ => ?_
    have hsub : Set.pi Set.univ s ⊆ Set.pi Set.univ fun i => toMeasurable (μ i) (s i) :=
      Set.pi_mono fun i _ => subset_toMeasurable (μ i) (s i)
    have hbox := h (fun i => toMeasurable (μ i) (s i)) fun i => measurableSet_toMeasurable _ _
    simp only [measure_toMeasurable] at hbox
    calc (K⁻¹ • ν.toOuterMeasure) (Set.pi Set.univ s)
        = K⁻¹ * ν (Set.pi Set.univ s) := rfl
      _ ≤ K⁻¹ * ν (Set.pi Set.univ fun i => toMeasurable (μ i) (s i)) := by
          gcongr
      _ ≤ K⁻¹ * (K * ∏ i, μ i (s i)) := by gcongr
      _ = ∏ i, (μ i).toOuterMeasure (s i) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel h0 h1, one_mul]
          rfl
  refine Measure.le_iff.2 fun A hA => ?_
  have hA' := hout A
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_def, toMeasure_apply _ _ hA]
  calc ν A = K * (K⁻¹ * ν A) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel h0 h1, one_mul]
    _ ≤ K * OuterMeasure.pi (fun i => (μ i).toOuterMeasure) A := by
        gcongr
        exact hA'

theorem exp_sub_one_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x - 1 ≤ 2 * x := by
  have hq := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  have hsq : x ^ 2 ≤ x := by nlinarith
  have := (abs_le.mp hq).2
  linarith

open scoped Matrix.Norms.Frobenius in

theorem dOp_chart_le {n : ℕ} {ε : Fin n → Bool} {s : ℝ} {E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ}
    (hE : ∀ i j, ((E i * (E j)ᴴ).trace).re = if i = j then 1 else 0) (hs : 0 ≤ s)
    (hn : Real.exp (2 * n ^ 2 * s) ≤ 2) (a a' : UJ ε) (t t' : Fin (n ^ 2) → ℝ)
    (ht : ∀ i, |t i| ≤ s) (ht' : ∀ i, |t' i| ≤ s)
    (ha : uMat a = (List.ofFn fun i => NormedSpace.exp ((t i : ℂ) • E i)).prod)
    (ha' : uMat a' = (List.ofFn fun i => NormedSpace.exp ((t' i : ℂ) • E i)).prod) :
    dOp (uMat (a * a'⁻¹)) ≤ Real.log 2 := by
  classical

  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hTc : Continuous (T : Matrix (Fin n) (Fin n) ℂ → _) :=
    LinearMap.continuous_of_finiteDimensional T.toAlgEquiv.toLinearEquiv.toLinearMap

  have hEn : ∀ i, ‖T (E i)‖ ≤ 1 := by
    intro i
    have hF : ‖E i‖ = 1 := by
      have h2 : ‖E i‖ ^ 2 = 1 := by
        rw [← GlobalTheory.ProductChart.ip_self, GlobalTheory.ProductChart.ip_apply, hE i i, if_pos rfl]
      nlinarith [norm_nonneg (E i)]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    have hv : T (E i) v = WithLp.toLp 2 (E i *ᵥ WithLp.ofLp v) := rfl
    rw [hv, ← Matrix.frobenius_norm_replicateCol (ι := Unit), Matrix.replicateCol_mulVec, one_mul]
    calc ‖E i * Matrix.replicateCol Unit (WithLp.ofLp v)‖
        ≤ ‖E i‖ * ‖Matrix.replicateCol Unit (WithLp.ofLp v)‖ := Matrix.frobenius_norm_mul _ _
      _ = ‖v‖ := by rw [hF, one_mul, Matrix.frobenius_norm_replicateCol]

  have himg : ∀ (u : UJ ε) (x : Fin (n ^ 2) → ℝ),
      uMat u = (List.ofFn fun i => NormedSpace.exp ((x i : ℂ) • E i)).prod →
      T (uMat u) = (List.ofFn fun i => NormedSpace.exp
        ((ContinuousLinearMap.proj i : (Fin (n ^ 2) → ℝ) →L[ℝ] ℝ) x • T (E i))).prod := by
    intro u x hu
    rw [hu, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp only [Function.comp_apply, ContinuousLinearMap.proj_apply]
    calc T (NormedSpace.exp ((x i : ℂ) • E i)) = NormedSpace.exp (T ((x i : ℂ) • E i)) :=
          NormedSpace.map_exp T hTc _
      _ = NormedSpace.exp (x i • T (E i)) := by rw [map_smul, Complex.coe_smul]
  obtain ⟨-, B, hB, hBn, -, -, -⟩ := GlobalTheory.ProductChart.exists_deriv_prod hs t' (n ^ 2) (fun i => T (E i))
    (fun i => ContinuousLinearMap.proj i) hEn ht'
  obtain ⟨-, -, -, -, hPn, -, -⟩ := GlobalTheory.ProductChart.exists_deriv_prod hs t (n ^ 2) (fun i => T (E i))
    (fun i => ContinuousLinearMap.proj i) hEn ht
  rw [← himg a' t' ha'] at hB
  rw [← himg a t ha] at hPn

  have hmul : uMat (a * a'⁻¹) = uMat a * uMat a'⁻¹ := rfl
  have hr : uMat a' * uMat a'⁻¹ = 1 := by
    first
      | exact Units.mul_inv (a' : (Matrix (Fin n) (Fin n) ℂ)ˣ)
      | simp [uMat]
  have hinv : T (uMat a'⁻¹) = B := by
    calc T (uMat a'⁻¹) = (B * T (uMat a')) * T (uMat a'⁻¹) := by rw [hB, one_mul]
      _ = B * T (uMat a' * uMat a'⁻¹) := by rw [map_mul, mul_assoc]
      _ = B := by rw [hr, map_one, mul_one]
  have hprod : T (uMat (a * a'⁻¹)) = T (uMat a) * B := by rw [hmul, map_mul, hinv]
  have hclose := GlobalTheory.ProductChart.norm_mul_sub_one_le hPn hBn
  rw [← hprod, ← Real.exp_add] at hclose
  have hnorm : ‖T (uMat (a * a'⁻¹))‖ ≤ 2 := by
    have h1 : ‖(1 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have h3 : ‖T (uMat (a * a'⁻¹))‖ ≤
        ‖T (uMat (a * a'⁻¹)) - 1‖ + ‖(1 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ := by
      simpa using norm_add_le (T (uMat (a * a'⁻¹)) - 1) 1
    have h4 : ((n ^ 2 : ℕ) : ℝ) * s + ((n ^ 2 : ℕ) : ℝ) * s = 2 * n ^ 2 * s := by push_cast; ring
    rw [h4] at hclose
    linarith
  have hd : dOp (uMat (a * a'⁻¹)) = Real.log ‖T (uMat (a * a'⁻¹))‖ := by
    unfold dOp
    rfl
  rw [hd]
  rcases (norm_nonneg (T (uMat (a * a'⁻¹)))).eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]
    exact Real.log_nonneg one_le_two
  · exact Real.log_le_log h0 hnorm

theorem lintegral_chart_all_le : ∀ (I : AutInst) (c : InfinitePlace I.F → ℝ) (s : ℝ) (E : InfinitePlace I.F → Fin (I.n ^ 2) → Matrix (Fin I.n) (Fin I.n) ℂ) (Θ : (InfinitePlace I.F → Fin (I.n ^ 2) → ℝ) → I.Ginf), (∀ v, IsGauge (I.ε v) (c v)) → (∀ v i, inG (I.ε v) (E v i)) → (∀ v i j, ((E v i * (E v j)ᴴ).trace).re = if i = j then 1 else 0) → 0 < s → 12 * (I.n : ℝ) ^ 3 * s ≤ 1 → 8 * (I.n : ℝ) ^ 5 * s ≤ 1 → (∀ t v, uMat (Θ t v) = (List.ofFn fun i => NormedSpace.exp ((t v i : ℂ) • E v i)).prod) → ∃ S : Set I.Ginf, MeasurableSet S ∧ (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) ∧ ∀ Φ : I.Ginf → ENNReal, Measurable Φ → ∫⁻ t in Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s), Φ (Θ t) ≤ ENNReal.ofReal (Real.exp I.f * ∏ v, c v) * ∫⁻ y in S, Φ y ∂(muInf I) := by
  intro I c s E Θ hc hG hE hs h12 h8 hΘ
  classical

  have hn0 : (0 : ℝ) ≤ I.n := Nat.cast_nonneg _
  have hnum : (I.n : ℝ) * (Real.exp (3 * (I.n : ℝ) ^ 2 * s) - 1) ≤ 1 / 2 ∧
      Real.exp (2 * (I.n : ℝ) ^ 2 * s) ≤ 2 ∧
      Real.exp (2 * (I.n : ℝ) ^ 3 * (Real.exp (2 * (I.n : ℝ) ^ 2 * s) - 1)) ≤ Real.exp 1 := by
    rcases Nat.eq_zero_or_pos I.n with h | h
    · simp only [h, Nat.cast_zero]
      norm_num
    · have hm : (1 : ℝ) ≤ I.n := by exact_mod_cast h
      have hsq : (I.n : ℝ) ^ 2 * s ≤ (I.n : ℝ) ^ 3 * s := by
        have : (I.n : ℝ) ^ 2 ≤ (I.n : ℝ) ^ 3 := by nlinarith
        nlinarith
      have hsq5 : (I.n : ℝ) ^ 5 * s = (I.n : ℝ) ^ 3 * ((I.n : ℝ) ^ 2 * s) := by ring
      have h3 : 3 * (I.n : ℝ) ^ 2 * s ≤ 1 := by nlinarith
      have h2 : 2 * (I.n : ℝ) ^ 2 * s ≤ 1 := by nlinarith
      have hp : 0 ≤ (I.n : ℝ) ^ 2 * s := by positivity
      have e3 := exp_sub_one_le (by positivity) h3
      have e2 := exp_sub_one_le (by positivity) h2
      refine ⟨?_, ?_, ?_⟩
      · have : (I.n : ℝ) * (Real.exp (3 * (I.n : ℝ) ^ 2 * s) - 1) ≤ (I.n : ℝ) * (2 * (3 * (I.n : ℝ) ^ 2 * s)) :=
          mul_le_mul_of_nonneg_left e3 hn0
        nlinarith
      · nlinarith
      · apply Real.exp_le_exp.2
        have hn3 : 0 ≤ 2 * (I.n : ℝ) ^ 3 := by positivity
        have := mul_le_mul_of_nonneg_left e2 hn3
        nlinarith
  obtain ⟨hchart, hexp2, hK1⟩ := hnum

  let C : Set (Fin (I.n ^ 2) → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s
  let Θv : ∀ v, (Fin (I.n ^ 2) → ℝ) → UJ (I.ε v) := fun v x => Θ (fun _ => x) v
  have hΘv : ∀ v x, uMat (Θv v x) = (List.ofFn fun i => NormedSpace.exp ((x i : ℂ) • E v i)).prod :=
    fun v x => hΘ (fun _ => x) v
  have hΘeq : ∀ t, Θ t = fun v => Θv v (t v) := by
    intro t
    funext v
    exact GlobalTheory.GaugeConst.uMat_injective (I.ε v) ((hΘ t v).trans (hΘv v (t v)).symm)
  have hcont : ∀ v, Continuous (Θv v) := by
    intro v
    have hE' : Continuous fun y : EuclideanSpace ℝ (Fin (I.n ^ 2)) => Θv v (WithLp.ofLp y) := by
      refine GlobalTheory.ProductChart.continuous_chart (E := E v) _ fun y => ?_
      rw [hΘv]
      simp only [Complex.coe_smul]
    exact hE'.comp (PiLp.continuous_toLp _ _)
  have hmeas : ∀ v, Measurable (Θv v) := fun v => (hcont v).measurable
  have hCc : IsCompact C := isCompact_univ_pi fun _ => isCompact_Icc
  let Sv : ∀ v, Set (UJ (I.ε v)) := fun v => Θv v '' C
  have hSv : ∀ v, MeasurableSet (Sv v) := fun v => ((hCc.image (hcont v)).isClosed).measurableSet
  refine ⟨Set.pi Set.univ Sv, MeasurableSet.univ_pi hSv, ?_, ?_⟩
  ·
    intro a ha a' ha' v
    obtain ⟨x, hx, hxa⟩ := ha v (Set.mem_univ v)
    obtain ⟨x', hx', hxa'⟩ := ha' v (Set.mem_univ v)
    have hb : ∀ y ∈ C, ∀ i, |y i| ≤ s := fun y hy i => by
      have hyi := hy i (Set.mem_univ i)
      rw [abs_of_nonneg hyi.1]
      exact hyi.2
    have e1 : uMat (a v) = (List.ofFn fun i => NormedSpace.exp ((x i : ℂ) • E v i)).prod := by
      rw [← hxa]
      exact hΘv v x
    have e2 : uMat (a' v) = (List.ofFn fun i => NormedSpace.exp ((x' i : ℂ) • E v i)).prod := by
      rw [← hxa']
      exact hΘv v x'
    exact dOp_chart_le (hE v) hs.le hexp2 (a v) (a' v) x x' (hb x hx) (hb x' hx') e1 e2
  · intro Φ hΦ

    set Kc := Real.exp (2 * (I.n : ℝ) ^ 3 * (Real.exp (2 * (I.n : ℝ) ^ 2 * s) - 1)) with hKc
    have hone : ∀ v (Ψ : UJ (I.ε v) → ENNReal), Measurable Ψ →
        ∫⁻ t in C, Ψ (Θv v t) ≤ ENNReal.ofReal (Kc * c v) * ∫⁻ y in Sv v, Ψ y ∂(muG (I.ε v)) :=
      fun v => GlobalTheory.ProductChart.lintegral_chart_le I.n (I.ε v) (c v) s (E v) (Θv v) (hc v) (hG v) (hE v)
        hs hchart (hΘv v)
    haveI : IsFiniteMeasure ((volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C) :=
      isFiniteMeasure_restrict.2 hCc.measure_lt_top.ne
    let ν : ∀ v, Measure (UJ (I.ε v)) := fun v => ((volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C).map (Θv v)
    let μS : ∀ v, Measure (UJ (I.ε v)) := fun v => (muG (I.ε v)).restrict (Sv v)
    have hfac : ∀ v (A : Set (UJ (I.ε v))), MeasurableSet A → ν v A ≤ ENNReal.ofReal (Kc * c v) * μS v A := by
      intro v A hA
      have hind : Measurable (A.indicator (1 : UJ (I.ε v) → ENNReal)) := measurable_one.indicator hA
      calc ν v A = ∫⁻ y, A.indicator 1 y ∂(ν v) := (lintegral_indicator_one hA).symm
        _ = ∫⁻ t in C, A.indicator 1 (Θv v t) := lintegral_map hind (hmeas v)
        _ ≤ ENNReal.ofReal (Kc * c v) * ∫⁻ y in Sv v, A.indicator 1 y ∂(muG (I.ε v)) := hone v _ hind
        _ = ENNReal.ofReal (Kc * c v) * μS v A := by rw [lintegral_indicator_one hA]
    set K : ENNReal := ∏ v, ENNReal.ofReal (Kc * c v) with hK
    have hbox : ∀ A : ∀ v, Set (UJ (I.ε v)), (∀ v, MeasurableSet (A v)) →
        Measure.pi ν (Set.pi Set.univ A) ≤ K * ∏ v, μS v (A v) := by
      intro A hA
      rw [Measure.pi_pi, hK, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod' fun v _ => hfac v (A v) (hA v)
    have hle : Measure.pi ν ≤ K • Measure.pi μS := by
      by_cases hK0 : K = 0
      · have h0 : Measure.pi ν = 0 := by
          rw [← Measure.measure_univ_eq_zero, ← Set.pi_univ]
          have := hbox (fun _ => Set.univ) fun _ => MeasurableSet.univ
          rw [hK0, zero_mul] at this
          exact le_antisymm this zero_le
        rw [h0]
        exact Measure.zero_le _
      · exact le_smul_pi (Measure.pi ν) μS hK0
          (ENNReal.prod_ne_top fun v _ => ENNReal.ofReal_ne_top) hbox

    have hKle : K ≤ ENNReal.ofReal (Real.exp I.f * ∏ v, c v) := by
      by_cases hc0 : ∀ v, 0 ≤ c v
      · have hKc0 : 0 ≤ Kc := (Real.exp_pos _).le
        rw [hK, ← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg hKc0 (hc0 v)]
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun v _ => hc0 v)
        have hcard : Fintype.card (InfinitePlace I.F) ≤ I.f := by
          have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)
          have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := I.F)
          have h3 : I.f = Module.finrank ℚ I.F := by unfold AutInst.f; rfl
          omega
        calc Kc ^ Fintype.card (InfinitePlace I.F) ≤ Real.exp 1 ^ Fintype.card (InfinitePlace I.F) :=
              pow_le_pow_left₀ hKc0 hK1 _
          _ = Real.exp (Fintype.card (InfinitePlace I.F) * 1) := (Real.exp_nat_mul _ _).symm
          _ ≤ Real.exp I.f := by
              apply Real.exp_le_exp.2
              rw [mul_one]
              exact_mod_cast hcard
      · push_neg at hc0
        obtain ⟨v, hv⟩ := hc0
        have : ENNReal.ofReal (Kc * c v) = 0 :=
          ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hv.le)
        rw [hK, Finset.prod_eq_zero (Finset.mem_univ v) this]
        exact zero_le

    have hvol : (volume : Measure (InfinitePlace I.F → Fin (I.n ^ 2) → ℝ)).restrict
        (Set.pi Set.univ fun _ => C) = Measure.pi fun _ => (volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C := by
      rw [show (volume : Measure (InfinitePlace I.F → Fin (I.n ^ 2) → ℝ)) =
        Measure.pi fun _ => (volume : Measure (Fin (I.n ^ 2) → ℝ)) from rfl, Measure.restrict_pi_pi]
    have hmapm : Measurable fun t : InfinitePlace I.F → Fin (I.n ^ 2) → ℝ => fun v => Θv v (t v) :=
      measurable_pi_lambda _ fun v => (hmeas v).comp (measurable_pi_apply v)
    have hmap : (Measure.pi fun _ => (volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C).map
        (fun t v => Θv v (t v)) = Measure.pi ν :=
      Measure.pi_map_pi fun v => (hmeas v).aemeasurable
    have hmu : (muInf I).restrict (Set.pi Set.univ Sv) = Measure.pi μS := by
      rw [show muInf I = Measure.pi fun v => muG (I.ε v) from rfl, Measure.restrict_pi_pi]
    calc ∫⁻ t in Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s), Φ (Θ t)
        = ∫⁻ t, Φ (fun v => Θv v (t v)) ∂(Measure.pi fun _ =>
            (volume : Measure (Fin (I.n ^ 2) → ℝ)).restrict C) := by
          have hset : (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s) =
              Set.pi Set.univ fun _ : InfinitePlace I.F => C := rfl
          rw [hset, hvol]
          exact lintegral_congr fun t => by rw [hΘeq t]
      _ = ∫⁻ y, Φ y ∂(Measure.pi ν) := by rw [← hmap, lintegral_map hΦ hmapm]
      _ ≤ ∫⁻ y, Φ y ∂(K • Measure.pi μS) := lintegral_mono' hle le_rfl
      _ = K * ∫⁻ y in Set.pi Set.univ Sv, Φ y ∂(muInf I) := by
          rw [lintegral_smul_measure, hmu, smul_eq_mul]
      _ ≤ ENNReal.ofReal (Real.exp I.f * ∏ v, c v) * ∫⁻ y in Set.pi Set.univ Sv, Φ y ∂(muInf I) := by
          gcongr

end GlobalTheory.ProductChartAll
