import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelicStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothContinuousConvolutionRealPointsUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalL2BoundHeightStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.SmoothGrowth

theorem integrableOn_of_sq {X : Type} [MeasurableSpace X] (μ : Measure X) (U : Set X) (hU : μ U ≠ ⊤)
    (h : X → ℂ) (hm : AEStronglyMeasurable h μ) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∫⁻ g in U, (‖h g‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (c ^ 2)) :
    IntegrableOn h U μ ∧ ∫ g in U, ‖h g‖ ∂μ ≤ c * Real.sqrt (μ U).toReal := by
  have h2 : eLpNorm h 2 (μ.restrict U) ≤ ENNReal.ofReal c := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have e : ENNReal.ofReal c = (ENNReal.ofReal (c ^ 2)) ^ (1 / (2 : ENNReal).toReal) := by
      rw [ENNReal.ofReal_pow hc, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [e]
    refine ENNReal.rpow_le_rpow (le_trans (le_of_eq ?_) hb) (by norm_num)
    refine lintegral_congr fun g => ?_
    rw [← ENNReal.rpow_natCast]
    norm_num [enorm]
  have e2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict U) (p := 1) (q := 2)
    (f := h) (by norm_num) hm.restrict
  rw [Measure.restrict_apply_univ] at e2
  have e3 : eLpNorm h 1 (μ.restrict U) ≤ ENNReal.ofReal (c * Real.sqrt (μ U).toReal) := by
    refine e2.trans ?_
    rw [ENNReal.ofReal_mul hc]
    refine mul_le_mul' h2 (le_of_eq ?_)
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hU]
    norm_num
  rw [eLpNorm_one_eq_lintegral_enorm] at e3
  have hi : IntegrableOn h U μ := ⟨hm.restrict, lt_of_le_of_lt e3 ENNReal.ofReal_lt_top⟩
  refine ⟨hi, ?_⟩
  rw [integral_norm_eq_lintegral_enorm hm.restrict]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) e3

theorem integrable_mul_of_support {X : Type} [MeasurableSpace X] (μ : Measure X) (U : Set X)
    (hU : MeasurableSet U) (h φ : X → ℂ) (hφ : AEStronglyMeasurable φ μ) (M : ℝ) (hM : ∀ x, ‖φ x‖ ≤ M)
    (hs : ∀ x, x ∉ U → φ x = 0) (hi : IntegrableOn h U μ) :
    Integrable (fun g => φ g * h g) μ ∧ ‖∫ g, φ g * h g ∂μ‖ ≤ M * ∫ g in U, ‖h g‖ ∂μ := by
  have h1 : IntegrableOn (fun g => φ g * h g) U μ :=
    Integrable.bdd_mul (c := M) hi hφ.restrict (Filter.Eventually.of_forall hM)
  have hz : ∀ x, x ∉ U → φ x * h x = 0 := fun x hx => by rw [hs x hx, zero_mul]
  refine ⟨h1.integrable_of_forall_notMem_eq_zero hz, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hi.norm.const_mul M) (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hM g) (norm_nonneg _)

theorem continuous_of_smoothInf (I : AutInst) (a : I.Ginf → ℂ) (ha : SmoothInf I a) : Continuous a := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨F, hF, he⟩ := ha x
  have hc : Continuous fun g : I.Ginf => (fun v i j => uMat (g v) i j :
      InfinitePlace I.F → Fin I.n → Fin I.n → ℂ) := by
    refine continuous_pi fun v => continuous_pi fun i => continuous_pi fun j => ?_
    have h1 : Continuous fun g : UJ (I.ε v) => uMat g := Units.continuous_val.comp continuous_subtype_val
    exact (h1.comp (continuous_apply v)).matrix_elem i j
  exact (hF.continuousAt.comp (f := fun g : I.Ginf => (fun v i j => uMat (g v) i j :
      InfinitePlace I.F → Fin I.n → Fin I.n → ℂ)) hc.continuousAt).congr (he.mono fun _ h => h.symm)

theorem continuous_of_open_invariant {X G : Type} [TopologicalSpace X] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K : Set G) (hK : IsOpen K) (h1 : (1 : G) ∈ K) (f : X × G → ℂ)
    (hc : ∀ b, Continuous fun z => f (z, b)) (hi : ∀ k ∈ K, ∀ z b, f (z, b * k) = f (z, b)) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h2 : ContinuousAt (fun p : X × G => f (p.1, x.2)) x := ((hc x.2).comp continuous_fst).continuousAt
  refine h2.congr ?_
  have h3 : IsOpen {p : X × G | x.2⁻¹ * p.2 ∈ K} := hK.preimage (by fun_prop)
  filter_upwards [h3.mem_nhds (by simpa using h1 : x ∈ {p : X × G | x.2⁻¹ * p.2 ∈ K})] with p hp
  rw [← hi _ hp]
  simp

theorem locallyIntegrable_partial {X Z : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Z] (μ : Measure X) (ν : Measure Z) [SFinite μ] [SFinite ν]
    (K : Set Z) (hK : MeasurableSet K) (e : Z → ℂ) (he : AEStronglyMeasurable e ν) (M : ℝ) (hM : ∀ k, ‖e k‖ ≤ M)
    (hs : ∀ k, k ∉ K → e k = 0) (h : X × Z → ℂ)
    (hi : ∀ V, IsCompact V → IntegrableOn h (V ×ˢ K) (μ.prod ν)) :
    LocallyIntegrable (fun z => ∫ k, e k * h (z, k) ∂ν) μ := by
  refine locallyIntegrable_iff.2 fun V hV => ?_
  have h1 := hi V hV
  rw [IntegrableOn, ← Measure.prod_restrict] at h1
  have h2 : Integrable (fun p : X × Z => e p.2 * h p) ((μ.restrict V).prod (ν.restrict K)) :=
    Integrable.bdd_mul (c := M) h1
      (he.restrict.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
      (Filter.Eventually.of_forall fun p => hM p.2)
  have h3 := h2.integral_prod_left
  refine h3.congr (Filter.Eventually.of_forall fun z => ?_)
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => by rw [hs k hk, zero_mul]

section Group

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [MeasurableSpace G₁] [MeasurableSpace G₂]
  [MeasurableMul G₁] [MeasurableMul G₂] (μ₁ : Measure G₁) (μ₂ : Measure G₂) [SFinite μ₁] [SFinite μ₂]
  [μ₁.IsMulLeftInvariant] [μ₂.IsMulLeftInvariant]

theorem conv_right_invariant [MeasurableMul (G₁ × G₂)] (a : G₁ → ℂ) (e : G₂ → ℂ) (Y : G₁ × G₂ → ℂ) (k : G₂) (hk : ∀ b, e (k * b) = e b)
    (x : G₁ × G₂) :
    ∫ g, (a g.1 * e g.2) * Y (x * (1, k) * g) ∂(μ₁.prod μ₂) = ∫ g, (a g.1 * e g.2) * Y (x * g) ∂(μ₁.prod μ₂) := by
  rw [← integral_mul_left_eq_self (μ := μ₁.prod μ₂) (fun g => (a g.1 * e g.2) * Y (x * g)) (1, k)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Prod.fst_mul, Prod.snd_mul, one_mul, hk, mul_assoc]

omit [MeasurableMul G₂] [μ₂.IsMulLeftInvariant] in

theorem conv_eq_partial (a : G₁ → ℂ) (e : G₂ → ℂ) (Y : G₁ × G₂ → ℂ) (z : G₁) (b : G₂)
    (hi : Integrable (fun g => (a g.1 * e g.2) * Y ((z, b) * g)) (μ₁.prod μ₂)) :
    ∫ g, (a g.1 * e g.2) * Y ((z, b) * g) ∂(μ₁.prod μ₂) =
      ∫ g, (∫ k, e k * Y ((1, b) * (g, k)) ∂μ₂) * a (z⁻¹ * g) ∂μ₁ := by
  rw [integral_prod _ hi, ← integral_mul_left_eq_self (μ := μ₁)
    (fun g => (∫ k, e k * Y ((1, b) * (g, k)) ∂μ₂) * a (z⁻¹ * g)) z]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [Prod.mk_mul_mk, one_mul, inv_mul_cancel_left]
  ring

end Group

theorem weak_integral_fixed {X Z H : Type} [MeasurableSpace X] [MeasurableSpace Z]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (μ : Measure X) (ν : Measure Z) [SFinite μ] [SFinite ν]
    (r : X × Z → H) (s : X → H) (a : X → ℂ) (e : Z → ℂ) (he : ∫ k, e k ∂ν = 1)
    (hr : ∀ g k, e k ≠ 0 → r (g, k) = s g) (u : H) :
    ∫ p, (a p.1 * e p.2) * ⟪u, r p⟫_ℂ ∂(μ.prod ν) = ∫ g, a g * ⟪u, s g⟫_ℂ ∂μ := by
  have h : (fun p : X × Z => (a p.1 * e p.2) * ⟪u, r p⟫_ℂ) = fun p => (a p.1 * ⟪u, s p.1⟫_ℂ) * e p.2 := by
    funext p
    by_cases h0 : e p.2 = 0
    · simp [h0]
    · rw [← hr p.1 p.2 h0]; ring
  rw [h, integral_prod_mul (fun g => a g * ⟪u, s g⟫_ℂ) e, he, mul_one]

theorem inv_tau_le (I : AutInst) (hn : 1 ≤ I.n) (h1 : (1 : I.Gf) ∈ I.Kset) (m : ℕ) (z : I.Ginf) (b : I.Gf) :
    (tau1 I (z, b))⁻¹ ^ m ≤ (tau1 I (1, b))⁻¹ ^ m * Real.exp ((m / I.f : ℝ) * dSum I z) := by
  obtain ⟨hp, -, -, hl⟩ := GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties I hn
  have h := (abs_le.1 (hl (1, b) (z, 1) h1)).1
  simp only [Prod.mk_mul_mk, one_mul, mul_one] at h
  have e : (m / I.f : ℝ) * dSum I z = m * (dSum I z / I.f) := by ring
  rw [e, Real.exp_nat_mul, ← mul_pow]
  refine pow_le_pow_left₀ (inv_nonneg.2 (hp _).le) ?_ m
  rw [← Real.exp_log (hp (z, b)), ← Real.exp_log (hp (1, b)), ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

theorem convolutionSmoothL2 : ConvolutionSmoothL2 := by
  intro B g hn hg a ha hac
  obtain ⟨hT2, hL, hS, hKc, -, ⟨K₀, hK₀⟩, hlev⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hKo, ⟨K, hK⟩, -⟩ := hlev g hg
  obtain ⟨hR1, hmul, hnorm, hcont, hext⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  haveI : (muInf B.I).IsHaarMeasure := by unfold muInf; infer_instance
  haveI : SigmaFinite (muInf B.I) := by unfold muInf; infer_instance
  haveI : BorelSpace B.I.GA := inferInstance
  have hμ : B.I.muA B.μf = (muInf B.I).prod B.μf := rfl
  haveI : (B.I.muA B.μf).IsMulLeftInvariant := by rw [hμ]; infer_instance
  haveI : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by rw [hμ]; infer_instance
  have hsub : B.I.Kg g ⊆ B.I.Kset := fun _ h => h.1
  have hKcl : IsClosed (B.I.Kg g) := by
    rw [← hK] at hKo ⊢; exact K.isClosed_of_isOpen hKo
  have hKcomp : IsCompact (B.I.Kg g) := hKc.of_isClosed_subset hKcl hsub
  have h1K : (1 : B.I.Gf) ∈ B.I.Kg g := by rw [← hK]; exact K.one_mem
  have hKpos : B.μf (B.I.Kg g) ≠ 0 := (hKo.measure_pos B.μf ⟨1, h1K⟩).ne'
  have hKfin : B.μf (B.I.Kg g) ≠ ⊤ := hKcomp.measure_lt_top.ne
  have hKm : MeasurableSet (B.I.Kg g) := hKo.measurableSet
  set c : ℂ := (((B.μf (B.I.Kg g)).toReal : ℝ) : ℂ)⁻¹ with hc
  set e : B.I.Gf → ℂ := (B.I.Kg g).indicator fun _ => c with he
  have he0 : ∀ k, k ∉ B.I.Kg g → e k = 0 := fun k hk => Set.indicator_of_notMem hk _
  have heM : ∀ k, ‖e k‖ ≤ ‖c‖ := fun k => norm_indicator_le_norm_self _ _
  have hei : Integrable e B.μf := (integrable_indicator_iff hKm).2 (integrableOn_const hKfin)
  have he1 : ∫ k, e k ∂B.μf = 1 := by
    rw [he, integral_indicator_const _ hKm, hc, Complex.real_smul, Measure.real]
    exact mul_inv_cancel₀ (by exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨hKpos, hKfin⟩)
  have hek : ∀ k ∈ B.I.Kg g, ∀ b, e (k * b) = e b := by
    intro k hk b
    have : k * b ∈ B.I.Kg g ↔ b ∈ B.I.Kg g := by
      rw [← hK] at hk ⊢; exact K.mul_mem_cancel_left hk
    by_cases hb : b ∈ B.I.Kg g
    · rw [he, Set.indicator_of_mem hb, Set.indicator_of_mem (this.2 hb)]
    · rw [he0 _ hb, he0 _ (fun h => hb (this.1 h))]
  have hacont : Continuous a := continuous_of_smoothInf B.I a ha
  have hai : Integrable a (muInf B.I) := hacont.integrable_of_hasCompactSupport hac
  obtain ⟨M, hM⟩ := hacont.bounded_above_of_compact_support hac
  have hφi : Integrable (fun p : B.I.GA => a p.1 * e p.2) (B.I.muA B.μf) := hai.mul_prod hei
  set m : ℕ := 2 * B.I.n ^ 2 * B.I.f with hm
  have hpos := (GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties B.I hn).1

  have hloc : ∀ V : Set B.I.Ginf, IsCompact V → ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : B.I.L2 B.μf B.fund) (x : B.I.GA),
      IntegrableOn (fun p => B.I.ext y (x * p)) (V ×ˢ B.I.Kg g) (B.I.muA B.μf) ∧
      ∫ p in V ×ˢ B.I.Kg g, ‖B.I.ext y (x * p)‖ ∂(B.I.muA B.μf) ≤ C * (tau1 B.I x)⁻¹ ^ m * ‖y‖ := by
    intro V hV
    have hU : IsCompact (V ×ˢ B.I.Kg g) := hV.prod hKcomp
    obtain ⟨C, hC, hb⟩ := GlobalTheory.T.local_L2_bound_height B _ hn hU fun u hu => hsub hu.2
    refine ⟨Real.sqrt C * Real.sqrt (B.I.muA B.μf (V ×ˢ B.I.Kg g)).toReal, by positivity, fun y x => ?_⟩
    have hτ : 0 ≤ (tau1 B.I x)⁻¹ := inv_nonneg.2 (hpos x).le
    have hsq : (Real.sqrt C * (tau1 B.I x)⁻¹ ^ m * ‖y‖) ^ 2 =
        C * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f) * ‖y‖ ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hC, ← pow_mul, hm]
      congr 3; ring
    obtain ⟨h1, h2⟩ := integrableOn_of_sq (B.I.muA B.μf) _ hU.measure_lt_top.ne (fun p => B.I.ext y (x * p))
      ((hext y).2.comp_measurePreserving (measurePreserving_mul_left _ x))
      (Real.sqrt C * (tau1 B.I x)⁻¹ ^ m * ‖y‖) (by positivity) (by rw [hsq]; exact hb y x)
    exact ⟨h1, h2.trans (le_of_eq (by ring))⟩
  obtain ⟨C, hC, hb⟩ := hloc _ hac.isCompact
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  refine ⟨M * ‖c‖ * C, fun y hy T hT => ?_⟩
  set f : B.I.GA → ℂ := fun x => ∫ p, (a p.1 * e p.2) * B.I.ext y (x * p) ∂(B.I.muA B.μf) with hf
  have hmain : ∀ x, Integrable (fun p : B.I.GA => (a p.1 * e p.2) * B.I.ext y (x * p)) (B.I.muA B.μf) ∧
      ‖f x‖ ≤ M * ‖c‖ * C * (tau1 B.I x)⁻¹ ^ m * ‖y‖ := by
    intro x
    obtain ⟨h1, h2⟩ := integrable_mul_of_support (B.I.muA B.μf) (tsupport a ×ˢ B.I.Kg g)
      ((isClosed_tsupport a).measurableSet.prod hKm) _ (fun p : B.I.GA => a p.1 * e p.2) hφi.1 (M * ‖c‖)
      (fun p => by rw [norm_mul]; exact mul_le_mul (hM _) (heM _) (norm_nonneg _) hM0)
      (fun p hp => by
        by_cases h : p.2 ∈ B.I.Kg g
        · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp ⟨h', h⟩), zero_mul]
        · rw [he0 _ h, mul_zero]) (hb y x).1
    refine ⟨h1, h2.trans ?_⟩
    refine (mul_le_mul_of_nonneg_left (hb y x).2 (by positivity)).trans (le_of_eq (by ring))
  have hright : ∀ k ∈ B.I.Kg g, ∀ x, f (x * (1, k)) = f x := fun k hk x =>
    conv_right_invariant (muInf B.I) B.μf a e (B.I.ext y) k (hek k hk) x
  have hsm : ∀ b, SmoothInf B.I (fun z => f (z, b)) ∧ Continuous fun z => f (z, b) := by
    intro b
    have e1 : (fun z => f (z, b)) = fun z =>
        ∫ p, (∫ k, e k * B.I.ext y ((1, b) * (p, k)) ∂B.μf) * a (z⁻¹ * p) ∂(muInf B.I) := by
      funext z
      exact conv_eq_partial (muInf B.I) B.μf a e (B.I.ext y) z b (hmain (z, b)).1
    rw [e1]
    refine GlobalTheory.T.smooth_continuous_convolution_realPointsUnitary B.I a _ ha hac ?_
    refine locallyIntegrable_partial (muInf B.I) B.μf (B.I.Kg g) hKm e hei.1 ‖c‖ heM he0
      (fun p => B.I.ext y ((1, b) * p)) fun V hV => ?_
    obtain ⟨C', -, hb'⟩ := hloc V hV
    exact (hb' y (1, b)).1
  refine ⟨f, ⟨fun γ hγ x => ?_, hright, fun b => ⟨(hsm b).1, ?_⟩⟩, ?_, fun x => (hmain x).2, ?_⟩
  · refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_mul_left (B.I.muA B.μf) x).quasiMeasurePreserving.ae (hext y).1] with p hp
    rw [mul_assoc γ, hp γ hγ]
  · refine ⟨M * ‖c‖ * C * (tau1 B.I (1, b))⁻¹ ^ m * ‖y‖, (m / B.I.f : ℝ), fun z => (hmain (z, b)).2.trans ?_⟩
    have h := inv_tau_le B.I hn (hsub h1K) m z b
    have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ M * ‖c‖ * C * ‖y‖)
    linarith
  · refine continuous_of_open_invariant (B.I.Kg g) hKo h1K f (fun b => (hsm b).2) fun k hk z b => ?_
    simpa using hright k hk (z, b)
  · have hU : IsURep B.R := ⟨hR1, hmul, hnorm, hcont⟩
    obtain ⟨T', hT', -⟩ := hU.exists_isOpOf hφi
    have hTT : T y = T' y := by
      refine ext_inner_left ℂ fun u => ?_
      rw [hT.2, hT'.2]
      refine (weak_integral_fixed (muInf B.I) B.μf (fun p => B.R p y) (fun z => B.R (z, 1) y) a e he1
        (fun z k hk => ?_) u).symm
      have hk' : k ∈ B.I.Kg g := by by_contra h; exact hk (he0 k h)
      have : ((z, k) : B.I.GA) = (z, 1) * (1, k) := by simp
      rw [this, hmul, ContinuousLinearMap.mul_apply, hy k hk']
    rw [hTT]
    exact (GlobalTheory.T.rightConvolution_operator_ae_eq_integral_adelic B _ T' hT' y).2

end GlobalTheory.SmoothGrowth
