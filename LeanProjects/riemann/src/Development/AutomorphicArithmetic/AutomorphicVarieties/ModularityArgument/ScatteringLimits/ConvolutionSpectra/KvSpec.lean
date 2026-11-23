import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.AeIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem ker_bd {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {κ : ℝ → V →L[ℂ] W} (h : HasCompactSupport κ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R < |t| → κ t = 0 := by
  obtain ⟨R, hR⟩ := h.isCompact.isBounded.exists_norm_le
  refine ⟨|R|, abs_nonneg _, fun t ht => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
  exact absurd ((hR t hm).trans (le_abs_self R)) (not_le.2 ht)

private theorem meas {V Z : Type} [NormedAddCommGroup V] [NormedAddCommGroup Z] {μ : Measure ℝ} (G : ℝ → V → Z)
    (hG : Continuous fun z : ℝ × V => G z.1 z.2) (u : ℝ → V) (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun y => G y (u y)) μ :=
  hG.comp_aestronglyMeasurable (f := fun y => (y, u y)) (aestronglyMeasurable_id.prodMk hu)

private theorem joint {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (k : V →L[ℂ] L W) : Continuous fun z : ℝ × V => sh W (-z.1) (k z.2) :=
  Continuous.compMeasurePreservingLp (f := fun z : ℝ × V => k z.2)
    (g := fun z : ℝ × V => (⟨fun x => x + -z.1, by fun_prop⟩ : C(ℝ, ℝ))) (k.continuous.comp continuous_snd)
    (ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.add (continuous_fst.comp continuous_fst).neg))
    (fun z => measurePreserving_add_right volume (-z.1)) (by simp)

theorem UpperTheory.V.Z.IntegralApplyAeEq.kvSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → (∀ e, (∀ᵐ x : ℝ, kv κ e x = κ (-x) e) ∧ Bdd (kv κ e) ∧ ∫ x, kv κ e x = symb κ 0 e) ∧
      ∀ (a b : ℝ) (u : L V), IntegrableOn (fun y => sh W (-y) (kv κ (u y))) (Ioc a b) ∧
        conv κ (cut V (Ioc a b) u) = ∫ y in Ioc a b, sh W (-y) (kv κ (u y)) := by
  intro V _ _ _ _ W _ _ _ _ κ hk
  have hc : ∀ e : V, Continuous fun x : ℝ => κ (-x) e := fun e => (hk.1.comp continuous_neg).clm_apply continuous_const
  have hs : ∀ e : V, HasCompactSupport fun x : ℝ => κ (-x) e := fun e =>
    (hk.2.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun A : V →L[ℂ] W => A e) rfl
  have hm : ∀ e : V, MemLp (fun x : ℝ => κ (-x) e) 2 volume := fun e => (hc e).memLp_of_hasCompactSupport (hs e)
  let A : V →ₗ[ℂ] L W :=
    { toFun := fun e => (hm e).toLp _
      map_add' := fun e f => by rw [← MemLp.toLp_add]; congr 1; funext x; simp
      map_smul' := fun c e => by rw [RingHom.id_apply, ← MemLp.toLp_const_smul]; congr 1; funext x; simp }
  have sp := Classical.epsilon_spec (p := fun C : V →L[ℂ] L W => ∀ e, ∀ᵐ x : ℝ, C e x = κ (-x) e)
    ⟨LinearMap.toContinuousLinearMap A, fun e => (hm e).coeFn_toLp⟩
  change ∀ e, ∀ᵐ x : ℝ, kv κ e x = κ (-x) e at sp
  obtain ⟨R, -, hR⟩ := ker_bd hk.2
  have hk1 : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
  refine ⟨fun e => ⟨sp e, ⟨R, ((cutLaws (V := W) (Icc (-R) R) univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 _).2 ?_⟩, ?_⟩,
    fun a b u => ?_⟩
  · filter_upwards [sp e] with x hx hx'
    rw [hx, hR _ (by rw [abs_neg]; exact not_le.1 fun h => hx' (abs_le.1 h)), ContinuousLinearMap.zero_apply]
  · rw [integral_congr_ae (sp e), integral_neg_eq_self (fun x => κ x e), symb]
    simp only [zero_mul, Complex.exp_zero, one_smul]
    rw [ContinuousLinearMap.integral_apply hk1]
  · have hu : IntegrableOn (u : ℝ → V) (Ioc a b) := integrableOn_Lp_of_measure_ne_top u (by norm_num) measure_Ioc_lt_top.ne
    have hI : IntegrableOn (fun y => sh W (-y) (kv κ (u y))) (Ioc a b) := by
      refine (hu.norm.const_mul ‖kv κ‖).mono' (meas (fun y e => sh W (-y) (kv κ e)) (joint (kv κ)) _ hu.1)
        (Eventually.of_forall fun y => ?_)
      rw [show ‖sh W (-y) (kv κ (u y))‖ = ‖kv κ (u y)‖ from (shF W).norm _ _]
      exact (kv κ).le_opNorm _
    refine ⟨hI, Lp.ext ?_⟩
    have m1 : Continuous fun z : ℝ × ℝ => κ (-(z.2 + -z.1)) := hk.1.comp (by fun_prop)
    have m2 : StronglyMeasurable fun z : ℝ × ℝ => (u : ℝ → V) z.1 := (Lp.stronglyMeasurable u).comp_measurable measurable_fst
    have m3 : AEStronglyMeasurable (fun z : ℝ × ℝ => κ (-(z.2 + -z.1)) (u z.1)) ((volume.restrict (Ioc a b)).prod volume) :=
      (ContinuousLinearMap.apply ℂ W).flip.aestronglyMeasurable_comp₂ m1.aestronglyMeasurable m2.aestronglyMeasurable
    have m4 : ∀ y : ℝ, ∀ᵐ x : ℝ, sh W (-y) (kv κ (u y)) x = κ (-(x + -y)) (u y) := fun y => by
      filter_upwards [sh_ae W (-y) (kv κ (u y)),
        (measurePreserving_add_right volume (-y)).quasiMeasurePreserving.ae (sp (u y))] with x p q
      rw [p, q]
    have h1 : ∀ᵐ x : ℝ, (∫ y in Ioc a b, sh W (-y) (kv κ (u y)) : L W) x = ∫ y in Ioc a b, κ (-(x + -y)) (u y) :=
      ae_integral (volume.restrict (Ioc a b)) (fun y => sh W (-y) (kv κ (u y))) hI (fun z => κ (-(z.2 + -z.1)) (u z.1)) m3
        (Eventually.of_forall m4)
    filter_upwards [h1, (convSpec κ hk (cut V (Ioc a b) u)).1] with x p q
    rw [p, q, ← integral_indicator measurableSet_Ioc,
      ← integral_add_left_eq_self ((Ioc a b).indicator fun y => κ (-(x + -y)) (u y)) x]
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae (cutSpec (Ioc a b) measurableSet_Ioc u)] with t ht
    rw [ht]
    by_cases h : x + t ∈ Ioc a b
    · simp only [indicator_of_mem h]
      congr 2
      ring
    · simp only [indicator_of_notMem h, map_zero]
