import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.OmMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LocFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutSpec

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private def chi (T : ℝ) (n : ℕ) (x : ℝ) : ℝ := max 0 (min (min 1 ((n + 1) * (x - T))) (T + n + 2 - x))

private theorem chi_cont (T : ℝ) (n : ℕ) : Continuous (chi T n) := by
  unfold chi
  fun_prop

private theorem chi_low (T : ℝ) (n : ℕ) {x : ℝ} (h : x ≤ T) : chi T n x = 0 := by
  unfold chi
  refine max_eq_left ?_
  have : ((n : ℝ) + 1) * (x - T) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  exact (min_le_left _ _).trans ((min_le_right _ _).trans this)

private theorem chi_high (T : ℝ) (n : ℕ) {x : ℝ} (h : T + n + 2 ≤ x) : chi T n x = 0 := by
  unfold chi
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

private theorem chi_nonneg (T : ℝ) (n : ℕ) (x : ℝ) : 0 ≤ chi T n x := le_max_left _ _

private theorem chi_le (T : ℝ) (n : ℕ) (x : ℝ) : chi T n x ≤ 1 :=
  max_le zero_le_one ((min_le_left _ _).trans (min_le_left _ _))

private theorem chi_supp (T : ℝ) (n : ℕ) : HasCompactSupport (chi T n) :=
  HasCompactSupport.intro (isCompact_Icc (a := T) (b := T + n + 2)) fun x hx => by
    rcases le_or_gt x T with h | h
    · exact chi_low T n h
    · exact chi_high T n (by
        by_contra h'
        exact hx ⟨h.le, (not_le.1 h').le⟩)

private theorem chi_one (T : ℝ) {x : ℝ} (h : T < x) : ∀ᶠ n : ℕ in atTop, chi T n x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (1 / (x - T)) (x - T))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hp : 0 < x - T := sub_pos.2 h
  have hn' : (N : ℝ) ≤ n := Nat.cast_le.2 hn
  have h1 : 1 / (x - T) ≤ n := ((le_max_left _ _).trans hN).trans hn'
  have h2 : x - T ≤ n := ((le_max_right _ _).trans hN).trans hn'
  have h3 : 1 ≤ ((n : ℝ) + 1) * (x - T) := by
    have := (div_le_iff₀ hp).1 h1
    nlinarith
  unfold chi
  rw [min_eq_left h3, min_eq_left (by linarith)]
  exact max_eq_right zero_le_one

private theorem sum_ae {α ι E : Type*} {m : MeasurableSpace α} {ν : Measure α} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → Lp E 2 ν) :
    ∀ᵐ x ∂ν, ((∑ i ∈ s, f i : Lp E 2 ν) : α → E) x = ∑ i ∈ s, (f i : α → E) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero E 2 ν] with x hx
    rw [Finset.sum_empty, hx]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

private theorem eu_sum {d : ℕ} (v : Eu d) : ∑ i, v i • (EuclideanSpace.single i (1 : ℂ) : Eu d) = v := by
  have := (EuclideanSpace.basisFun (Fin d) ℂ).sum_repr v
  simpa using this

private theorem ae_down {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (w : L2 μ)
    (E : Set (RightCosetSpace (Gam K (2 + 2)))) (hE : MeasurableSet E)
    (h : ∀ᵐ y ∂μ, mk (Gam K (2 + 2)) y ∈ E →
      (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) = 0) :
    ∀ᵐ p ∂quotientMeasure (Gam K (2 + 2)) μ, p ∈ E → (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) p = 0 := by
  have hm : MeasurableSet (E ∩ {p | (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) p ≠ 0}) :=
    hE.inter ((Lp.stronglyMeasurable w).measurable (measurableSet_singleton 0).compl)
  have h0 : ∫⁻ p, (E ∩ {p | (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) p ≠ 0}).indicator 1 p
      ∂quotientMeasure (Gam K (2 + 2)) μ = 0 := by
    rw [lintegral_quotientMeasure]
    refine (lintegral_congr_ae (g := 0) (ae_restrict_of_ae ?_)).trans (by simp)
    filter_upwards [h] with y hy
    exact indicator_of_notMem (fun hA => hA.2 (hy hA.1)) _
  rw [lintegral_indicator_one hm] at h0
  exact ae_iff.2 (measure_mono_null (fun p hp => _root_.not_imp.1 hp) h0)

private theorem first {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d)
    (T : ℝ) (c : L (Eu d)) (hc : ∀ᵐ x : ℝ, x ≤ T → c x = 0) :
    ∀ᵐ y ∂μ, Om T y → (A.J c : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) = 0 := by
  let E : Set (RightCosetSpace (Gam K (2 + 2))) := {p | Om T (Quotient.out p : G1 K (2 + 2))}
  have hEm : MeasurableSet E := (omMeas T).2.2
  have hmk : ∀ y : G1 K (2 + 2), mk (Gam K (2 + 2)) y ∈ E ↔ Om T y := fun y => by
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (RightCosetSpace.mk (Gam K (2 + 2)) y))
    change Om T (Quotient.out (RightCosetSpace.mk (Gam K (2 + 2)) y)) ↔ Om T y
    rw [← hγ]
    exact (omMeas T).1 _ γ.2 y
  let R := LpToLpRestrictCLM (RightCosetSpace (Gam K (2 + 2))) ℂ ℂ (quotientMeasure (Gam K (2 + 2)) μ) 2 E
  have hR : ∀ w : L2 μ, R w = 0 ↔ ∀ᵐ p ∂quotientMeasure (Gam K (2 + 2)) μ, p ∈ E →
      (w : RightCosetSpace (Gam K (2 + 2)) → ℂ) p = 0 := fun w => by
    rw [Lp.eq_zero_iff_ae_eq_zero, ← ae_restrict_iff' hEm]
    constructor
    · intro h
      filter_upwards [h, LpToLpRestrictCLM_coeFn ℂ E w] with p h1 h2
      rw [← h2, h1]
      rfl
    · intro h
      filter_upwards [h, LpToLpRestrictCLM_coeFn ℂ E w] with p h1 h2
      rw [h2, h1]
      rfl
  let Φ := R.comp A.J.toContinuousLinearMap
  let Sp : Submodule ℂ (L (Eu d)) := LinearMap.ker Φ.toLinearMap
  have hcl : IsClosed (Sp : Set (L (Eu d))) := by
    have : (Sp : Set (L (Eu d))) = {x | Φ x = 0} := by
      ext x
      simp [Sp]
    rw [this]
    exact isClosed_eq Φ.continuous continuous_const
  have hsub : Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d), Continuous β ∧ HasCompactSupport β ∧
      (∀ x, x ≤ T → β x = 0) ∧ ∀ᵐ x : ℝ, u x = β x • v} ≤ Sp := by
    refine Submodule.span_le.2 ?_
    rintro g ⟨β, v, h1, h2, h3, h4⟩
    refine (hR (A.J g)).2 (ae_down μ _ E hEm ?_)
    filter_upwards [A.spec β v g h1 h2 h4] with y hy hyE
    rw [hy]
    unfold theta
    refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
    rw [h3 _ ((hmk y).1 hyE q), zero_mul, zero_mul]
  have hin := closure_mono hsub ((denseCc d).2.2 T c hc)
  rw [hcl.closure_eq] at hin
  have hz : R (A.J c) = 0 := hin
  filter_upwards [(quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae ((hR _).1 hz)] with y hy hO
  exact hy ((hmk y).2 hO)

private theorem th_chi {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d)
    (T : ℝ) (U : ℝ → Eu d) (χ : ℝ → ℝ) (h0 : ∀ x ≤ T, χ x = 0) (y : G1 K (2 + 2)) :
    ∑ i, theta (fun x => (χ x : ℂ) * U x i) (A.sec (EuclideanSpace.single i (1 : ℂ))) y =
      th (fun z => (χ (HH z) : ℂ) * secF A.sec U z) y := by
  have fin : ∀ i : Fin d, (Function.support fun q : Cos K =>
      bf (fun x => (χ x : ℂ) * U x i) (A.sec (EuclideanSpace.single i (1 : ℂ))) ((q.out : G1 K (2 + 2)) * y)).Finite := fun i => by
    refine (locFin {y} T isCompact_singleton).subset fun q hq => ⟨y, rfl, ?_⟩
    by_contra hlt
    apply hq
    have e : χ (HP 2 2 ((q.out : G1 K (2 + 2)) * y)) = 0 := h0 _ (not_le.1 hlt).le
    simp only [bf, e]
    simp
  simp only [theta_eq]
  unfold th
  rw [← finsum_sum_comm _ _ fun i _ => fin i]
  refine finsum_congr fun q => ?_
  generalize ((q.out : G1 K (2 + 2)) * y) = z
  have hs : A.sec (U (HH z)) z = ∑ i, U (HH z) i * A.sec (EuclideanSpace.single i (1 : ℂ)) z := by
    conv_lhs => rw [← eu_sum (U (HH z))]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
  have ex : ((((2 + 2 : ℕ) : ℝ) / 2 * HP 2 2 z : ℝ) : ℂ) = 2 * (HH z : ℂ) := by
    push_cast
    ring
  simp only [bf, secF, ex, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem rep_chi {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d)
    (T : ℝ) (U : ℝ → Eu d) (hU : Continuous U) (χ : ℝ → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (h0 : ∀ x ≤ T, χ x = 0) :
    ∃ w : L (Eu d), (∀ᵐ x : ℝ, w x = (χ x : ℂ) • U x) ∧
      Reps μ (A.J w) (th fun z => (χ (HH z) : ℂ) * secF A.sec U z) := by
  have hβ : ∀ i : Fin d, Continuous fun x => (χ x : ℂ) * U x i := fun i =>
    (Complex.continuous_ofReal.comp hχ).mul ((EuclideanSpace.proj i : Eu d →L[ℂ] ℂ).continuous.comp hU)
  have hβc : ∀ i : Fin d, HasCompactSupport fun x => (χ x : ℂ) * U x i := fun i =>
    (hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).mul_right
  have hex := fun i => (denseCc d).2.1 _ (EuclideanSpace.single i (1 : ℂ)) (hβ i) (hβc i)
  choose u hu using hex
  refine ⟨∑ i, u i, ?_, ?_⟩
  · filter_upwards [sum_ae Finset.univ u, ae_all_iff.2 hu] with x h1 h2
    rw [h1, Finset.sum_congr rfl fun i _ => h2 i]
    simp only [mul_smul, ← Finset.smul_sum, eu_sum]
  · have h2 := ae_all_iff.2 fun i => A.spec _ _ (u i) (hβ i) (hβc i) (hu i)
    have h3 := (quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae (sum_ae Finset.univ fun i => A.J (u i))
    unfold Reps
    filter_upwards [h2, h3] with y a b
    rw [map_sum, b, Finset.sum_congr rfl fun i _ => a i]
    exact th_chi μ A T U χ h0 y

private theorem th_lim {K : Type} [Field K] [NumberField K] (T : ℝ) (G : G1 K (2 + 2) → ℂ) (y : G1 K (2 + 2)) :
    ∀ᶠ n : ℕ in atTop, th (fun z => (chi T n (HH z) : ℂ) * G z) y = th (hi T G) y := by
  have h1 := (Filter.eventually_all_finite (l := (atTop : Filter ℕ)) (locFin {y} T isCompact_singleton)
    (p := fun q n => (chi T n (HH ((q.out : G1 K (2 + 2)) * y)) : ℂ) * G ((q.out : G1 K (2 + 2)) * y) =
      hi T G ((q.out : G1 K (2 + 2)) * y))).2 fun q _ => by
    by_cases h : T < HH ((q.out : G1 K (2 + 2)) * y)
    · filter_upwards [chi_one T h] with n hn
      rw [hn, hi, indicator_of_mem (show _ ∈ {z | T < HH z} from h)]
      simp
    · refine Eventually.of_forall fun n => ?_
      rw [chi_low T n (not_lt.1 h), hi, indicator_of_notMem (show _ ∉ {z | T < HH z} from h)]
      simp
  filter_upwards [h1] with n hn
  unfold th
  refine finsum_congr fun q => ?_
  by_cases hq : T ≤ HH ((q.out : G1 K (2 + 2)) * y)
  · exact hn q ⟨y, rfl, hq⟩
  · have h' : ¬ T < HH ((q.out : G1 K (2 + 2)) * y) := fun h => hq h.le
    beta_reduce
    rw [chi_low T n (not_lt.1 h'), hi, indicator_of_notMem (show _ ∉ {z | T < HH z} from h')]
    simp

private theorem nsq {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (u : L V) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner u u)]
  simp only [inner_self_eq_norm_sq]

private theorem cut_lim {d : ℕ} (T : ℝ) (u c : L (Eu d)) (w : ℕ → L (Eu d))
    (hc : ∀ᵐ x : ℝ, c x = (Ioi T).indicator u x) (hw : ∀ n, ∀ᵐ x : ℝ, w n x = (chi T n x : ℂ) • u x) :
    Tendsto w atTop (𝓝 c) := by
  have hall := ae_all_iff.2 hw
  have hae : ∀ n, ∀ᵐ x : ℝ, ‖(w n - c : L (Eu d)) x‖ ^ 2 ≤ ‖u x‖ ^ 2 := fun n => by
    filter_upwards [Lp.coeFn_sub (w n) c, hc, hw n] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    by_cases h : T < x
    · rw [indicator_of_mem (show x ∈ Ioi T from h)]
      have e : ((chi T n x : ℂ) • u x - u x) = ((chi T n x - 1 : ℝ) : ℂ) • u x := by
        push_cast
        rw [sub_smul, one_smul]
      rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [abs_le]
      constructor <;> linarith [chi_nonneg T n x, chi_le T n x]
    · rw [indicator_of_notMem (show x ∉ Ioi T from h), chi_low T n (not_lt.1 h)]
      simp
  have hlim : ∀ᵐ x : ℝ, Tendsto (fun n => ‖(w n - c : L (Eu d)) x‖ ^ 2) atTop (𝓝 0) := by
    have hsub := ae_all_iff.2 fun n => Lp.coeFn_sub (w n) c
    filter_upwards [hsub, hc, hall] with x h1 h2 h3
    refine tendsto_const_nhds.congr' ?_
    by_cases h : T < x
    · filter_upwards [chi_one T h] with n hn
      beta_reduce
      rw [h1 n, Pi.sub_apply, h2, h3 n, hn, indicator_of_mem (show x ∈ Ioi T from h)]
      simp
    · refine Eventually.of_forall fun n => ?_
      beta_reduce
      rw [h1 n, Pi.sub_apply, h2, h3 n, indicator_of_notMem (show x ∉ Ioi T from h), chi_low T n (not_lt.1 h)]
      simp
  have hi2 : Integrable fun x => ‖u x‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  have h1 := tendsto_integral_of_dominated_convergence (F := fun n x => ‖(w n - c : L (Eu d)) x‖ ^ 2) (f := fun _ => 0)
    (fun x => ‖u x‖ ^ 2) (fun n => (Lp.aestronglyMeasurable (w n - c)).norm.pow 2) hi2
    (fun n => by
      filter_upwards [hae n] with x hx
      rwa [Real.norm_of_nonneg (sq_nonneg _)]) hlim
  have h3 : (fun n => ∫ x, ‖(w n - c : L (Eu d)) x‖ ^ 2) = fun n => ‖w n - c‖ ^ 2 := funext fun n => (nsq _).symm
  rw [h3, integral_zero] at h1
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
  rw [Real.sqrt_zero] at h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact h2.congr fun n => by
    rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cutRep :
    ForAllC fun K _ _ μ _ _ _ _ _ _ d _ A _ => ∀ (T : ℝ) (u : L (Eu d)), (∀ᵐ y ∂μ, Om T y → (A.J (cut (Eu d) (Ioi T) u) : RightCosetSpace (Gam K (2 + 2)) → ℂ) (mk (Gam K (2 + 2)) y) = 0) ∧
      ∀ U : ℝ → Eu d, Continuous U → (∀ᵐ s : ℝ, u s = U s) → Reps μ (A.J (cut (Eu d) (Ioi T) u)) (th (hi T (secF A.sec U))) := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' T u
  have hc := cutSpec (V := Eu d) (Ioi T) measurableSet_Ioi u
  refine ⟨first μ A T _ ?_, fun U hU hu => ?_⟩
  · filter_upwards [hc] with x hx h
    rw [hx]
    exact indicator_of_notMem (fun h' : x ∈ Ioi T => not_lt.2 h h') _
  have hex := fun n : ℕ => rep_chi μ A T U hU (chi T n) (chi_cont T n) (chi_supp T n) fun x hx => chi_low T n hx
  choose w hw hr using hex
  have hlim : Tendsto w atTop (𝓝 (cut (Eu d) (Ioi T) u)) := cut_lim T u _ w hc fun n => by
    filter_upwards [hw n, hu] with x h1 h2
    rw [h1, h2]
  have hJ : Tendsto (fun n => A.J (w n)) atTop (𝓝 (A.J (cut (Eu d) (Ioi T) u))) :=
    (A.J.continuous.tendsto _).comp hlim
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hJ).exists_seq_tendsto_ae
  have h1 := (quasiMeasurePreserving_mk (Gam K (2 + 2)) μ).ae hae
  have h2 := ae_all_iff.2 hr
  unfold Reps
  filter_upwards [h1, h2] with y a b
  refine tendsto_nhds_unique a (tendsto_const_nhds.congr' ?_)
  filter_upwards [hns.tendsto_atTop.eventually (th_lim T (secF A.sec U) y)] with i hi'
  rw [b (ns i), hi']
