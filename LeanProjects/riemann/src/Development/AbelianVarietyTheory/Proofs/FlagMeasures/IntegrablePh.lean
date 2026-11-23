import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicKernelConvergencePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsContRepKernelIntegralCompactSupportStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DenseCompactlySupportedL2Statement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeFnSumSmulAeEq

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KernelExpansion

theorem exists_mem_of_dense {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H))] (S : Submodule ℂ H) (hS : Dense (S : Set H))
    (x : H) : ∃ g ∈ S, T g = T x := by
  have : FiniteDimensional ℂ (S.map (T : H →ₗ[ℂ] H)) :=
    Submodule.finiteDimensional_of_le LinearMap.map_le_range
  have hc : IsClosed ((fun z => T z) ⁻¹' (S.map (T : H →ₗ[ℂ] H) : Set H)) :=
    (Submodule.closed_of_finiteDimensional _).preimage T.continuous
  have hx : x ∈ closure (S : Set H) := hS x
  exact hc.closure_subset_iff.2 (fun z hz => ⟨z, hz, rfl⟩) hx

theorem exists_orthonormal {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range (T : H →ₗ[ℂ] H))]
    (hT : IsOrthProjOnto T (LinearMap.range (T : H →ₗ[ℂ] H))) (D : ℕ)
    (hD : Module.finrank ℂ (LinearMap.range (T : H →ₗ[ℂ] H)) = D) :
    ∃ y : Fin D → H, Orthonormal ℂ y ∧ Submodule.span ℂ (Set.range y) = LinearMap.range (T : H →ₗ[ℂ] H) ∧
      (∀ i, T (y i) = y i) ∧ ∀ g, T g = ∑ i, ⟪y i, g⟫_ℂ • y i := by
  subst hD
  let b := stdOrthonormalBasis ℂ (LinearMap.range (T : H →ₗ[ℂ] H))
  have hfix : ∀ i, T (b i : H) = b i := by
    intro i
    obtain ⟨z, hz⟩ := (b i).2
    have := congrArg (fun A : H →L[ℂ] H => A z) hT.1
    rw [← hz]
    exact this
  have hexp : ∀ g, T g = ∑ i, ⟪(b i : H), g⟫_ℂ • (b i : H) := by
    intro g
    have h := congrArg Subtype.val (b.sum_repr' ⟨T g, g, rfl⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hT.2.1, hfix]
  refine ⟨fun i => b i, b.orthonormal.comp_linearIsometry (Submodule.subtypeₗᵢ _), ?_, hfix, hexp⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b i).2
  · rintro _ ⟨g, rfl⟩
    show T g ∈ _
    rw [hexp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def compactSub {X : Type} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {y | ∃ C : Set X, IsCompact C ∧ ∀ᵐ z ∂μ, z ∉ C → (y : X → ℂ) z = 0}
  add_mem' := by
    rintro a b ⟨C, hC, ha⟩ ⟨C', hC', hb⟩
    refine ⟨C ∪ C', hC.union hC', ?_⟩
    filter_upwards [ha, hb, Lp.coeFn_add a b] with z h1 h2 h3 hz
    rw [Set.mem_union, not_or] at hz
    rw [h3, Pi.add_apply, h1 hz.1, h2 hz.2, add_zero]
  zero_mem' := ⟨∅, isCompact_empty, by
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z h _
    rw [h]; rfl⟩
  smul_mem' := by
    rintro c a ⟨C, hC, ha⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [ha, Lp.coeFn_smul c a] with z h1 h2 hz
    rw [h2, Pi.smul_apply, h1 hz, smul_zero]

theorem coeFn_sum_smul {X ι : Type} [MeasurableSpace X] (μ : Measure X) (s : Finset ι) (c : ι → ℂ)
    (y : ι → Lp ℂ 2 μ) (F : ι → X → ℂ) (h : ∀ i, (y i : X → ℂ) =ᵐ[μ] F i) :
    ((∑ i ∈ s, c i • y i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x => ∑ i ∈ s, c i * F i x := by
  first
  | exact @_root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq
  | exact _root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq
  | (apply _root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq ..)

theorem ae_eq_of_pairing {X ι : Type} [Fintype ι] [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ] (k : X → ℂ) (hk : Continuous k)
    (c : ι → ℂ) (y : ι → Lp ℂ 2 μ) (F : ι → X → ℂ) (hF : ∀ i, Continuous (F i))
    (h : ∀ i, (y i : X → ℂ) =ᵐ[μ] F i)
    (hp : ∀ g ∈ compactSub μ, ∫ z, k z * (g : X → ℂ) z ∂μ = ∑ i, ⟪y i, g⟫_ℂ * c i) :
    (fun z => k z - ∑ i, c i * star (F i z)) =ᵐ[μ] 0 := by
  have hc : ∀ i, Continuous fun z => c i * star (F i z) := fun i => continuous_const.mul (hF i).star
  refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    (hk.sub (continuous_finset_sum _ fun i _ => hc i)).locallyIntegrable fun s hs => ?_
  have hm : MeasurableSet s := hs.isClosed.measurableSet
  have hg := indicatorConstLp_coeFn (p := 2) (hs := hm) (hμs := hs.measure_lt_top.ne) (c := (1 : ℂ)) (μ := μ)
  have h1 := hp (indicatorConstLp 2 hm hs.measure_lt_top.ne (1 : ℂ)) ⟨s, hs, by
    filter_upwards [hg] with z hz hzs
    rw [hz, Set.indicator_of_notMem hzs]⟩
  have e : ∀ u : X → ℂ, ∫ z, u z * (indicatorConstLp 2 hm hs.measure_lt_top.ne (1 : ℂ) : Lp ℂ 2 μ) z ∂μ =
      ∫ z in s, u z ∂μ := by
    intro u
    rw [← integral_indicator hm]
    refine integral_congr_ae ?_
    filter_upwards [hg] with z hz
    rw [hz]
    by_cases hzs : z ∈ s <;> simp [hzs]
  rw [integral_sub (hk.continuousOn.integrableOn_compact hs)
    ((continuous_finset_sum _ fun i _ => hc i).continuousOn.integrableOn_compact hs),
    integral_finset_sum _ fun i _ => (hc i).continuousOn.integrableOn_compact hs, ← e, h1, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, ← e, mul_comm, L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h i] with z hz
  rw [hz]
  simp [mul_comm]

theorem integral_mul_star {X : Type} [MeasurableSpace X] (μ : Measure X) (y : Lp ℂ 2 μ) (F : X → ℂ)
    (h : (y : X → ℂ) =ᵐ[μ] F) (hy : ‖y‖ = 1) :
    Integrable (fun x => F x * star (F x)) μ ∧ ∫ x, F x * star (F x) ∂μ = 1 := by
  have e : (fun x => ⟪(y : X → ℂ) x, (y : X → ℂ) x⟫_ℂ) =ᵐ[μ] fun x => F x * star (F x) := by
    filter_upwards [h] with z hz
    rw [hz, RCLike.inner_apply]
    rfl
  refine ⟨(L2.integrable_inner y y).congr e, ?_⟩
  rw [← integral_congr_ae e, ← L2.inner_def, inner_self_eq_norm_sq_to_K, hy]
  simp

theorem norm_sum_sq_le {ι : Type} [Fintype ι] (c F : ι → ℂ) :
    ‖∑ i, c i * F i‖ ^ 2 ≤ (∑ i, ‖c i‖ ^ 2) * ‖∑ i, F i * star (F i)‖ := by
  have e : ∑ i, F i * star (F i) = ((∑ i, ‖F i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Complex.mul_conj' (F i)
  rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => ‖c i‖) (fun i => ‖F i‖))
  gcongr
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

theorem two_mul_rank_le {n : ℕ} (ε : Fin n → Bool) : 2 * rkR ε ≤ n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  unfold rkR
  omega

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d) (hdec : LocDec B h)
    (hb : HBig B 32 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hle, hi⟩ := GlobalTheory.T.discrete_series_coefficient_integrable_majorant B d h hd hdec
  have h1 := hi 0 le_rfl fun v => by
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with h0 | h0
    · exact Or.inl h0
    · right
      have h2 : (2 : ℝ) * rkR (B.I.ε v) ≤ B.I.n := by exact_mod_cast two_mul_rank_le _
      have h3 : (0 : ℝ) < rkR (B.I.ε v) := by exact_mod_cast h0
      have h4 := Real.sqrt_pos.2 h3
      refine lt_of_lt_of_le ?_ (hb v)
      have h5 : (B.I.n : ℝ) * rkR (B.I.ε v) < (B.I.n : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_lt_mul_of_pos_right h5 h4]
  refine h1.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
  simpa using hle g

theorem kernelB : KernelB := by
  intro B d h hd hn hdec hb hfin T hT
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  have : (Measure.pi fun v => Formalism.REAL.muG (B.I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  have : (B.I.muA B.μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  obtain ⟨-, -, -, hP⟩ := GlobalTheory.T.globalConvolutionOrthogonalProjector_proof B d hd (integrable_ph B d h hd hdec hb)
  obtain ⟨hproj, -, -, hfd, hD⟩ := hP T hT
  have := hfd hfin
  obtain ⟨hbd, hKc, hKi, -⟩ := GlobalTheory.T.automorphicKernel_convergence_properties B d h hd hn hdec hb
  obtain ⟨y, hy, hspan, hfix, hexp⟩ := exists_orthonormal T hproj B.D hD
  have hrep : ∀ g ∈ compactSub ((B.I.muA B.μf).restrict B.fund), IsContRep B (T g)
      (fun x => ∫ z in B.fund, kern B.I (phe B d) x z * (g : B.I.GA → ℂ) z ∂(B.I.muA B.μf)) := by
    rintro g ⟨C, hC, hg⟩
    exact GlobalTheory.T.isContRep_kernel_integral_compact_support B d h hd hn hdec hb T hT g C hC hg
  have huniq : ∀ (u : B.I.L2 B.μf B.fund) f f', IsContRep B u f → IsContRep B u f' → f' = f :=
    fun u f f' h1 h2 => (GlobalTheory.ExtContRep.ext_ae_eq_contRep B u f h1).2.1 f' h2
  have hF : ∀ i, ∃ F, IsContRep B (y i) F := by
    intro i
    obtain ⟨g, hg, e⟩ := exists_mem_of_dense T (compactSub _) (GlobalTheory.T.dense_compactly_supported_L2 B) (y i)
    exact ⟨_, hfix i ▸ e ▸ hrep g hg⟩
  choose F hF using hF
  have hK : ∀ x z, kern B.I (phe B d) x z = ∑ i, F i x * star (F i z) := by
    intro x z
    have hkx : Continuous fun z => kern B.I (phe B d) x z :=
      Continuous.comp (g := fun p : B.I.GA × B.I.GA => kern B.I (phe B d) p.1 p.2) (f := fun z => (x, z)) hKc
        (Continuous.prodMk_right x)
    have h0 := ae_eq_of_pairing ((B.I.muA B.μf).restrict B.fund) _ hkx (fun i => F i x) y F
      (fun i => (hF i).1) (fun i => (hF i).2.2) fun g hg => by
        have h1 : IsContRep B (T g) fun x => ∑ i, ⟪y i, g⟫_ℂ * F i x := by
          refine ⟨continuous_finset_sum _ fun i _ => continuous_const.mul (hF i).1, fun γ hγ x => ?_, ?_⟩
          · exact Finset.sum_congr rfl fun i _ => by rw [(hF i).2.1 γ hγ]
          · rw [hexp]
            exact coeFn_sum_smul _ _ _ y F fun i => (hF i).2.2
        exact congrFun (huniq _ _ _ h1 (hrep g hg)) x
    have z0 : IsContRep B 0 0 := ⟨continuous_const, fun _ _ _ => rfl, Lp.coeFn_zero _ _ _⟩
    have z1 : IsContRep B 0 fun z => kern B.I (phe B d) x z - ∑ i, F i x * star (F i z) := by
      refine ⟨hkx.sub (continuous_finset_sum _ fun i _ => continuous_const.mul (hF i).1.star),
        fun γ hγ w => ?_, (Lp.coeFn_zero _ _ _).trans h0.symm⟩
      beta_reduce
      rw [(hKi γ hγ x w).2]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [(hF i).2.1 γ hγ]
    exact sub_eq_zero.1 (congrFun (huniq _ _ _ z0 z1) z)
  have hI := fun i => integral_mul_star _ (y i) (F i) (hF i).2.2 (hy.1 i)
  refine ⟨y, F, hy, hspan, hF, hK, ?_, ?_, fun c x => ?_⟩
  · simp only [hK]
    exact integrable_finset_sum _ fun i _ => (hI i).1
  · simp only [hK]
    rw [integral_finset_sum _ fun i _ => (hI i).1]
    simp only [(hI _).2]
    simp
  · refine (norm_sum_sq_le c fun i => F i x).trans ?_
    rw [← hK]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_tsum_le_tsum_norm (hbd x x).1).trans ((hbd x x).2.trans (le_of_eq ?_))
    rw [mul_inv, ← sq, ← pow_mul]
    congr 2
    ring

end GlobalTheory.KernelExpansion
