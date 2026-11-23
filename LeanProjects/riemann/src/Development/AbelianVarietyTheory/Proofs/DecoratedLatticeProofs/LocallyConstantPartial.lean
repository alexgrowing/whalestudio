import Mathlib

noncomputable section

open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

namespace GlobalTheory.PartialIntegral

section Real

variable {X A : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup A] [NormedSpace ℝ A] (μ : Measure X) [μ.IsAddHaarMeasure]

theorem exists_majorant {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (k : ℕ) :
    ∃ b : X → ℝ, Integrable b μ ∧ ∀ x a, ‖a‖ ^ k * ‖F (x, a)‖ ≤ b x := by
  set N : ℕ := Module.finrank ℝ X + 1 with hN
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z : X × A, (1 + ‖z‖) ^ (k + N) * ‖F z‖ ≤ C := by
    have := fun z =>
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k + N, 0)) (k := k + N) (n := 0) le_rfl le_rfl F z
    simp only [norm_iteratedFDeriv_zero] at this
    exact ⟨_, this⟩
  refine ⟨fun x => C * (1 + ‖x‖) ^ (-(N : ℝ)), (integrable_one_add_norm (by rw [hN]; push_cast; linarith)).const_mul C,
    fun x a => ?_⟩
  have hp : 0 < 1 + ‖x‖ := by positivity
  show _ ≤ C * (1 + ‖x‖) ^ (-(N : ℝ))
  rw [Real.rpow_neg hp.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  refine le_trans ?_ (hC (x, a))
  have h1 : ‖a‖ ≤ 1 + ‖(x, a)‖ := by have := norm_snd_le (x, a); simp only at this; linarith
  have h2 : 1 + ‖x‖ ≤ 1 + ‖(x, a)‖ := by have := norm_fst_le (x, a); simp only at this; linarith
  rw [pow_add _ k N, mul_right_comm]
  gcongr

theorem continuous_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (a : A) :
    Continuous fun x => F (x, a) := F.continuous.comp (continuous_id.prodMk continuous_const)

theorem integrable_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (a : A) :
    Integrable (fun x => F (x, a)) μ := by
  obtain ⟨b, hb, h⟩ := exists_majorant μ F 0
  exact hb.mono' (continuous_slice F a).aestronglyMeasurable (Eventually.of_forall fun x => by simpa using h x a)

def dSnd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) : 𝓢(X × A, A →L[ℝ] E) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) ((ContinuousLinearMap.compL ℝ A (X × A) E).flip (ContinuousLinearMap.inr ℝ X A))
    (SchwartzMap.fderivCLM ℝ (X × A) E F)

theorem hasFDerivAt_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (x : X) (a : A) :
    HasFDerivAt (fun a => F (x, a)) (dSnd F (x, a)) a :=
  (F.differentiable (x, a)).hasFDerivAt.comp a (hasFDerivAt_prodMk_right x a)

theorem hasFDerivAt_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) (a : A) :
    HasFDerivAt (fun a => ∫ x, F (x, a) ∂μ) (∫ x, dSnd F (x, a) ∂μ) a := by
  obtain ⟨b, hb, h⟩ := exists_majorant μ (dSnd F) 0
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun a x => F (x, a)) (F' := fun a x => dSnd F (x, a))
    (s := Set.univ) (bound := b) univ_mem
    (Eventually.of_forall fun a => (continuous_slice F a).aestronglyMeasurable) (integrable_slice μ F a)
    (continuous_slice (dSnd F) a).aestronglyMeasurable
    (Eventually.of_forall fun x a _ => by simpa using h x a) hb
    (Eventually.of_forall fun x a _ => hasFDerivAt_slice F x a)

theorem smooth_decay (n : ℕ) : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)),
    ContDiff ℝ n (fun a => ∫ x, F (x, a) ∂μ) ∧
      ∀ k : ℕ, ∃ C : ℝ, ∀ a, ‖a‖ ^ k * ‖iteratedFDeriv ℝ n (fun a => ∫ x, F (x, a) ∂μ) a‖ ≤ C := by
  induction n with
  | zero =>
    intro E _ _ F
    refine ⟨contDiff_zero.2 (continuous_iff_continuousAt.2 fun a => (hasFDerivAt_integral μ F a).continuousAt), fun k => ?_⟩
    obtain ⟨b, hb, h⟩ := exists_majorant μ F k
    refine ⟨∫ x, b x ∂μ, fun a => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    calc ‖a‖ ^ k * ‖∫ x, F (x, a) ∂μ‖ ≤ ‖a‖ ^ k * ∫ x, ‖F (x, a)‖ ∂μ := by
          gcongr
          exact norm_integral_le_integral_norm _
      _ = ∫ x, ‖a‖ ^ k * ‖F (x, a)‖ ∂μ := (integral_const_mul _ _).symm
      _ ≤ _ := integral_mono ((integrable_slice μ F a).norm.const_mul _) hb fun x => h x a
  | succ n ih =>
    intro E _ _ F
    obtain ⟨h1, h2⟩ := ih _ (dSnd F)
    have e : fderiv ℝ (fun a => ∫ x, F (x, a) ∂μ) = fun a => ∫ x, dSnd F (x, a) ∂μ :=
      funext fun a => (hasFDerivAt_integral μ F a).fderiv
    refine ⟨?_, fun k => ?_⟩
    · rw [Nat.cast_succ, contDiff_succ_iff_fderiv, e]
      exact ⟨fun a => (hasFDerivAt_integral μ F a).differentiableAt, by simp, h1⟩
    · obtain ⟨C, hC⟩ := h2 k
      exact ⟨C, fun a => by rw [← norm_iteratedFDeriv_fderiv, e]; exact hC a⟩

def intFst {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : 𝓢(X × A, E)) : 𝓢(A, E) where
  toFun a := ∫ x, F (x, a) ∂μ
  smooth' := contDiff_infty.2 fun n => (smooth_decay μ n E F).1
  decay' k n := (smooth_decay μ n E F).2 k

theorem schwartz_partial [FiniteDimensional ℝ A] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(V, ℂ))
    (L₁ : X →ₗ[ℝ] V) (L₂ : A →ₗ[ℝ] V) (hL : ∀ x a, L₁ x + L₂ a = 0 → x = 0 ∧ a = 0) :
    (∀ a, Integrable (fun x => f (L₁ x + L₂ a)) μ) ∧ ∃ h : 𝓢(A, ℂ), ∀ a, h a = ∫ x, f (L₁ x + L₂ a) ∂μ := by
  let L : (X × A) →L[ℝ] V := LinearMap.toContinuousLinearMap (L₁.coprod L₂)
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith (L₁.coprod L₂)
    (LinearMap.ker_eq_bot'.2 fun z hz => Prod.ext (hL z.1 z.2 hz).1 (hL z.1 z.2 hz).2)
  let F : 𝓢(X × A, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ (g := L) L.hasTemperateGrowth hK f
  exact ⟨fun a => integrable_slice μ F a, intFst μ F, fun a => rfl⟩

end Real

section Finite

variable {Y B W : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] [TopologicalSpace B] [T2Space B] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  (ν : Measure Y) [ν.IsAddHaarMeasure]

theorem eventually_invariant {g : W → ℂ} (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g) :
    ∀ᶠ u in 𝓝 (0 : W), ∀ x, g (x + u) = g x := by
  have h : ∀ᶠ u in 𝓝 (0 : W), ∀ x ∈ tsupport g, g (x + u) = g x ∧ g (x - u) = g x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  filter_upwards [h] with u hu x
  by_cases hx : x ∈ tsupport g
  · exact (hu x hx).1
  · by_cases hx' : x + u ∈ tsupport g
    · have := (hu _ hx').2
      rw [add_sub_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem locallyConstant_partial {g : W → ℂ} (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g)
    {M₁ : Y → W} {M₂ : B → W} {Q₁ : W → Y} {Q₂ : W → B} (c₁ : Continuous M₁) (c₂ : Continuous M₂) (d₁ : Continuous Q₁)
    (d₂ : Continuous Q₂) (e₁ : ∀ y b, Q₁ (M₁ y + M₂ b) = y) (e₂ : ∀ y b, Q₂ (M₁ y + M₂ b) = b) :
    (∀ b, Integrable (fun y => g (M₁ y + M₂ b)) ν) ∧ IsLocallyConstant (fun b => ∫ y, g (M₁ y + M₂ b) ∂ν) ∧
      HasCompactSupport fun b => ∫ y, g (M₁ y + M₂ b) ∂ν := by
  refine ⟨fun b => ?_, ?_, ?_⟩
  · refine Continuous.integrable_of_hasCompactSupport (h1.continuous.comp (c₁.add continuous_const)) ?_
    refine HasCompactSupport.intro (h2.isCompact.image d₁) fun y hy => ?_
    by_contra h
    exact hy ⟨_, subset_tsupport g h, e₁ y b⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).2 fun b => ?_
    have ht : Tendsto (fun b' => M₂ b' - M₂ b) (𝓝 b) (𝓝 0) :=
      (c₂.sub continuous_const).tendsto' b 0 (sub_self _)
    filter_upwards [ht.eventually (eventually_invariant h1 h2)] with b' hb'
    congr 1
    funext y
    rw [← hb' (M₁ y + M₂ b)]
    congr 1
    abel
  · refine HasCompactSupport.intro (h2.isCompact.image d₂) fun b hb => ?_
    have : (fun y => g (M₁ y + M₂ b)) = fun _ => 0 := by
      funext y
      by_contra h
      exact hb ⟨_, subset_tsupport g h, e₂ y b⟩
    rw [this, integral_zero]

end Finite

theorem exists_integral_split {G X Y : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [LocallyCompactSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (e : G ≃ₜ+ X × Y) (m : Measure G) [m.IsAddHaarMeasure] (μ : Measure X) [μ.IsAddHaarMeasure] (ν : Measure Y)
    [ν.IsAddHaarMeasure] :
    ∃ c : ℂ, ∀ (u : X → ℂ) (v : Y → ℂ), Integrable u μ → Integrable v ν →
      Integrable (fun z => u (e z).1 * v (e z).2) m ∧
        ∫ z, u (e z).1 * v (e z).2 ∂m = c * ((∫ x, u x ∂μ) * ∫ y, v y ∂ν) := by
  haveI : (μ.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ ν
  haveI : (m.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map m
  have h := Measure.isAddLeftInvariant_eq_smul (m.map e) (μ.prod ν)
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  refine ⟨((Measure.addHaarScalarFactor (m.map e) (μ.prod ν) : ℝ) : ℂ), fun u v hu hv => ⟨?_, ?_⟩⟩
  · have : Integrable (fun z : X × Y => u z.1 * v z.2) (m.map e) := by
      rw [h]
      exact (hu.mul_prod hv).smul_measure_nnreal
    exact he.integrable_map_iff.1 this
  · rw [← he.integral_map (fun z : X × Y => u z.1 * v z.2)]
    conv_lhs => rw [h]
    rw [integral_smul_nnreal_measure, integral_prod_mul, NNReal.smul_def, Complex.real_smul]

end GlobalTheory.PartialIntegral

end
