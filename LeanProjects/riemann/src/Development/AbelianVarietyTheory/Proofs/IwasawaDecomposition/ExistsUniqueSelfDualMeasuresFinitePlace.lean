import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualOfDualSubgroups
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallDualLattices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx Filter
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SelfDualFinite

section Abstract

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V]

theorem integral_indicator_mul (μ : Measure V) [μ.IsAddHaarMeasure] (B : V → V → ℂ)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (M N : AddSubgroup V) (hMo : IsOpen (M : Set V))
    (hN : ∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) (y : V) :
    ∫ x, (M : Set V).indicator (fun _ => (1 : ℂ)) x * B x y ∂μ =
      (N : Set V).indicator (fun _ => (μ.real M : ℂ)) y := by
  classical
  by_cases hy : y ∈ N
  · rw [Set.indicator_of_mem (by exact hy)]
    have e1 : (fun x => (M : Set V).indicator (fun _ => (1 : ℂ)) x * B x y) =
        (M : Set V).indicator (fun _ => (1 : ℂ)) := by
      ext x
      by_cases hx : x ∈ M
      · rw [(hN _).1 hy x hx, mul_one]
      · simp [hx]
    rw [e1, integral_indicator_const _ hMo.measurableSet]
    simp
  · rw [Set.indicator_of_notMem (by exact hy)]
    rw [hN] at hy
    push Not at hy
    obtain ⟨n, hn, hn1⟩ := hy
    refine GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate μ _ n _ hn1 fun x => ?_
    have : (M : Set V).indicator (fun _ => (1 : ℂ)) (x + n) = (M : Set V).indicator (fun _ => (1 : ℂ)) x := by
      by_cases hx : x ∈ M
      · simp [hx, M.add_mem hx hn]
      · have : x + n ∉ M := fun h => hx (by simpa using M.sub_mem h hn)
        simp [hx, this]
    rw [this, ha]; ring

variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]

theorem integral_trunc (μ : Measure V) [μ.IsAddHaarMeasure] (B : V → V → ℂ)
    (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (M N : AddSubgroup V) (hMo : IsOpen (M : Set V))
    (hNo : IsOpen (N : Set V)) (hNc : IsCompact (N : Set V))
    (hM : ∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)
    (f : V → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (z : V) :
    ∫ y, (N : Set V).indicator (fun _ => (1 : ℂ)) y * ((∫ x, f x * B x y ∂μ) * B y z) ∂μ =
      (μ.real N : ℂ) * ∫ x in M, f (x - z) ∂μ := by
  set χ : V → ℂ := (N : Set V).indicator (fun _ => 1) with hχ
  have hχc : Continuous χ := (IsClopen.continuous_indicator ⟨hNc.isClosed, hNo⟩ continuous_const)
  have h1 : ∀ y, χ y * ((∫ x, f x * B x y ∂μ) * B y z) = ∫ x, f x * (χ y * B y (x + z)) ∂μ := by
    intro y
    rw [← integral_mul_const, ← integral_const_mul]
    congr 1; ext x
    rw [hs y (x + z), ha, hs y z]; ring
  have hsw : ∫ y, ∫ x, f x * (χ y * B y (x + z)) ∂μ ∂μ = ∫ x, ∫ y, f x * (χ y * B y (x + z)) ∂μ ∂μ := by
    refine integral_integral_swap (Continuous.integrable_of_hasCompactSupport ?_ ?_)
    · have : Continuous fun p : V × V => B p.1 (p.2 + z) :=
        hB.comp (f := fun p : V × V => (p.1, p.2 + z)) (by fun_prop)
      exact (hf.comp continuous_snd).mul ((hχc.comp continuous_fst).mul this)
    · refine HasCompactSupport.intro (hNc.prod hfc) ?_
      rintro ⟨y, x⟩ h
      simp only [Set.mem_prod, not_and_or] at h
      rcases h with h | h
      · simp [Function.uncurry, hχ, Set.indicator_of_notMem h]
      · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport h]
  have h2 : ∀ x, ∫ y, f x * (χ y * B y (x + z)) ∂μ =
      (M : Set V).indicator (fun w => (μ.real N : ℂ) * f (w - z)) (x + z) := by
    intro x
    rw [integral_const_mul, hχ, integral_indicator_mul μ B ha N M hNo
      (fun x => (hM x).trans (by simp only [hs x]))]
    by_cases hx : x + z ∈ (M : Set V)
    · simp [hx, mul_comm]
    · simp [hx]
  simp_rw [h1]
  rw [hsw]
  simp_rw [h2]
  rw [integral_add_right_eq_self (μ := μ) ((M : Set V).indicator (fun w => (μ.real N : ℂ) * f (w - z))) z,
    integral_indicator hMo.measurableSet, integral_const_mul]

theorem existsUnique_selfDual (B : V → V → ℂ)
    (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (h0 : ∀ y, B 0 y = 1) (hn : ∀ x y, ‖B x y‖ = 1)
    (H : ∀ U ∈ 𝓝 (0 : V), ∃ M N : AddSubgroup V, (M : Set V) ⊆ U ∧ IsOpen (M : Set V) ∧ IsCompact (M : Set V) ∧
      IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧ (∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) ∧
      (∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)) : ∃! μ : Measure V, SelfDual μ B := by
  classical
  obtain ⟨μ, hμ, hinv⟩ := GlobalTheory.JR.AbsInv.exists_selfDual B hB hs ha H
  have hsd : SelfDual μ B := by
    refine ⟨hμ, fun Φ hc hk hI z => ?_⟩
    obtain ⟨U, hU⟩ := (𝓝 (0 : V)).exists_antitone_basis
    choose M N hMU hMo hMc hNo hNc hN hM using fun k => H (U k) (hU.mem k)
    have hvol : ∀ k, μ.real (N k) * μ.real (M k) = 1 := by
      intro k
      have hcl : IsClopen (M k : Set V) := ⟨(hMc k).isClosed, hMo k⟩
      have hχc : Continuous ((M k : Set V).indicator (fun _ => (1 : ℂ))) :=
        hcl.continuous_indicator continuous_const
      have hχs : HasCompactSupport ((M k : Set V).indicator (fun _ => (1 : ℂ))) :=
        HasCompactSupport.intro (hMc k) fun x hx => by simp [hx]
      have hlc : IsLocallyConstant ((M k : Set V).indicator (fun _ => (1 : ℂ))) := by
        refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
        by_cases hx : x ∈ (M k : Set V)
        · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
        · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
          rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
      have e1 := hinv _ ⟨hlc, hχs⟩ 0
      rw [GlobalTheory.JR.AbsInv.fourB_fourB μ B hB hs ha (M k) (N k) (hMo k) (hNo k) (hNc k) (hN k) (hM k) _ hχc hχs
        (fun x m hm => ?_)] at e1
      · simp only [neg_zero, Set.indicator_of_mem (show (0 : V) ∈ (M k : Set V) from (M k).zero_mem),
          mul_one] at e1
        rw [mul_comm]; exact_mod_cast e1
      · by_cases hx : x ∈ M k
        · simp [hx, (M k).add_mem hx hm]
        · have : x + m ∉ M k := fun h => hx (by simpa using (M k).sub_mem h hm)
          simp [hx, this]
    have hBc : ∀ y, Continuous fun x => B x y := fun y =>
      hB.comp (f := fun x : V => (x, y)) (by fun_prop)
    have hev : ∀ y, ∀ᶠ k in atTop, y ∈ N k := by
      intro y
      have : {x | ‖B x y - 1‖ < 1 / 2} ∈ 𝓝 (0 : V) :=
        (isOpen_lt ((hBc y).sub continuous_const).norm continuous_const).mem_nhds (by simp [h0])
      filter_upwards [hU.eventually_subset this] with k hk
      refine (hN k y).2 fun x hx => GlobalTheory.CharConductor.eq_one_of_pow_near_one fun n => ?_
      have e : B x y ^ n = B (n • x) y := by
        induction n with
        | zero => simp [h0]
        | succ n ih => rw [pow_succ, ih, succ_nsmul, ha]
      rw [e]
      exact hk (hMU k ((M k).nsmul_mem hx n))
    have t1 : Tendsto (fun k => ∫ y, (N k : Set V).indicator (fun _ => (1 : ℂ)) y *
        ((∫ x, Φ x * B x y ∂μ) * B y z) ∂μ) atTop (𝓝 (∫ y, (∫ x, Φ x * B x y ∂μ) * B y z ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun y => ‖∫ x, Φ x * B x y ∂μ‖) (fun k => ?_) hI.norm
        (fun k => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
      · exact (aestronglyMeasurable_const.indicator (hNo k).measurableSet).mul
          (hI.1.mul (hBc z).aestronglyMeasurable)
      · by_cases hy : y ∈ (N k : Set V) <;> simp [hy, hn]
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev y] with k hk
        rw [Set.indicator_of_mem (by exact hk), one_mul]
    have t2 : Tendsto (fun k => (μ.real (N k) : ℂ) * ∫ x in M k, Φ (x - z) ∂μ) atTop (𝓝 (Φ (-z))) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hc' : Continuous fun x => Φ (x - z) := hc.comp (by fun_prop)
      have : {x | ‖Φ (x - z) - Φ (-z)‖ < ε / 2} ∈ 𝓝 (0 : V) :=
        (isOpen_lt (hc'.sub continuous_const).norm continuous_const).mem_nhds (by simp [hε])
      filter_upwards [hU.eventually_subset this] with k hk
      have hv : (μ.real (N k) : ℂ) * (μ.real (M k) : ℂ) = 1 := by exact_mod_cast hvol k
      have e : (μ.real (N k) : ℂ) * ∫ x in M k, Φ (x - z) ∂μ - Φ (-z) =
          (μ.real (N k) : ℂ) * ∫ x in M k, (Φ (x - z) - Φ (-z)) ∂μ := by
        rw [integral_sub (hc'.continuousOn.integrableOn_compact (hMc k))
          (continuousOn_const.integrableOn_compact (hMc k)), setIntegral_const, Complex.real_smul, mul_sub,
          ← mul_assoc, hv, one_mul]
      have b := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := fun x => Φ (x - z) - Φ (-z))
        (hMc k).measure_lt_top (fun x hx => le_of_lt (hk (hMU k hx)))
      rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg]
      calc _ ≤ μ.real (N k) * (ε / 2 * μ.real (M k)) := mul_le_mul_of_nonneg_left b measureReal_nonneg
        _ = ε / 2 := by rw [mul_left_comm, hvol, mul_one]
        _ < ε := by linarith
    refine tendsto_nhds_unique t1 (t2.congr fun k => ?_)
    exact (integral_trunc μ B hB hs ha (M k) (N k) (hMo k) (hNo k) (hNc k) (hM k) Φ hc hk z).symm
  refine ⟨μ, hsd, fun ν hν => ?_⟩
  obtain ⟨M, N, -, hMo, hMc, hNo, hNc, hN, -⟩ := H Set.univ univ_mem
  refine hsd.eq_of_test hν ((M : Set V).indicator (fun _ => (1 : ℂ)))
    (IsClopen.continuous_indicator ⟨hMc.isClosed, hMo⟩ continuous_const)
    (HasCompactSupport.intro hMc fun x hx => by simp [hx]) ?_ 0 (by simp)
  simp only [integral_indicator_mul μ B ha M N hMo hN]
  exact (integrable_indicator_iff hNo.measurableSet).2 (continuousOn_const.integrableOn_compact hNc)

end Abstract

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem existsUnique_of_bilin (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (hne : ∃ t, ψ t ≠ 1) (V : Type) [AddCommGroup V] [Module (Fv F v) V] [Module.Finite (Fv F v) V]
    [TopologicalSpace V] [IsModuleTopology (Fv F v) V] [IsTopologicalAddGroup V] [T2Space V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (β : LinearMap.BilinForm (Fv F v) V) (hs : ∀ x y, β x y = β y x) (hn : ∀ x, (∀ y, β x y = 0) → x = 0) :
    ∃! μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) := by
  letI : NontriviallyNormedField (Fv F v) :=
    Valued.toNontriviallyNormedField (Fv F v) (WithZero (Multiplicative ℤ))
  haveI : IsUltrametricDist (Fv F v) := inferInstance
  obtain ⟨n, hc⟩ := GlobalTheory.CharConductor.exists_exponent_of_valued ψ hψ hne
  obtain ⟨c, hcv⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp n)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hcv.symm.trans (map_zero _))
  have hstd : GlobalTheory.JR.IsStdChar (ψ.mulShift c) := by
    constructor
    · intro x hx
      exact (hc c).2 hcv.le x (Valued.toNormedField.norm_le_one_iff.1 hx)
    · obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
      have h1 : ¬ ∀ s : Fv F v, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (c * t * s) = 1 := by
        rw [hc, map_mul, hcv, ht, ← WithZero.exp_add, WithZero.exp_le_exp]
        omega
      push Not at h1
      obtain ⟨s, hs1, hs2⟩ := h1
      refine ⟨t * s, by rwa [AddChar.mulShift_apply, ← mul_assoc], fun y hy => ?_⟩
      rw [Valued.toNormedField.norm_lt_one_iff] at hy
      rw [Valued.toNormedField.norm_le_one_iff, mul_right_comm, map_mul]
      refine mul_le_one' ?_ hs1
      rw [map_mul, ht]
      rcases eq_or_ne (Valued.v y : WithZero (Multiplicative ℤ)) 0 with h | h
      · simp [h]
      · rw [← WithZero.exp_log h, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
        rw [← WithZero.exp_log h, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
  have hn' : ∀ x, (∀ y, (c⁻¹ • β) x y = 0) → x = 0 := fun x h => hn x fun y => by
    simpa [hc0] using h y
  have hs' : ∀ x y, (c⁻¹ • β) x y = (c⁻¹ • β) y x := fun x y => by simp [hs x y]
  have key := GlobalTheory.JR.exists_small_dual_lattices (Fv F v) _ hstd V (c⁻¹ • β) ⟨hs'⟩
    ⟨hn', fun y h => hn' y fun x => (hs' y x).trans (h x)⟩
  have e : ∀ x y, ψ.mulShift c ((c⁻¹ • β) x y) = ψ (β x y) := fun x y => by
    simp [AddChar.mulShift_apply, hc0]
  simp only [e] at key
  exact existsUnique_selfDual _ key.1 (fun x y => by rw [hs]) (fun x x' y => by simp [AddChar.map_add_eq_mul])
    (fun y => by simp) (fun x y => hu _) key.2

end Local

section Form

open GlobalTheory.SelfDualLatticeCompare

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (R : Type) [Field R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem sigR_smul (c : R) (z : R ⊗[F] E) : sigR R σ (c • z) = c • sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]
  | tmul a e => rfl

noncomputable def bilin (n : ℕ) : LinearMap.BilinForm R (Fin n → Fin M → R ⊗[F] E) :=
  LinearMap.mk₂ R (BR R σ J)
    (fun x x' y => by
      simp [BR, hR, Formalism.UG.hform, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp [BR, hR, Formalism.UG.hform, sigR_smul, Finset.mul_sum])
    (fun x y y' => by
      simp [BR, hR, Formalism.UG.hform, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp [BR, hR, Formalism.UG.hform, Finset.mul_sum])

variable {σ J}

theorem sigR_hR (h : IsCMExt F E σ) (hJ : IsHermND σ J) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  have hJ' : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR R h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ']
  ring

theorem BR_symm (h : IsCMExt F E σ) (hJ : IsHermND σ J) {n : ℕ} (x y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J x y = BR R σ J y x := by
  refine Finset.sum_congr rfl fun a _ => (algebraMap R (R ⊗[F] E)).injective ?_
  rw [trace_tensor R h, trace_tensor R h, sigR_hR R h hJ, sigR_hR R h hJ, add_comm]

theorem eq_zero_of_trace (h : IsCMExt F E σ) (z : R ⊗[F] E)
    (hz : ∀ c, Algebra.trace R (R ⊗[F] E) (c * z) = 0) : z = 0 := by
  have h1 : ∀ c, c * z + sigR R σ c * sigR R σ z = 0 := fun c => by
    rw [← map_mul, ← trace_tensor R h, hz, map_zero]
  obtain ⟨e, he⟩ : ∃ e : E, σ e ≠ e := by
    by_contra hc
    push Not at hc
    have hsurj : Function.Surjective (algebraMap F E) := fun e => exists_of_conj_eq h e (hc e)
    have := (LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨(algebraMap F E).injective, hsurj⟩).finrank_eq
    rw [h.2.2.1] at this
    simp at this
  have h2 := h1 1
  have h3 := h1 (inclR R e)
  have h4 : sigR R σ (inclR R e) = inclR R (σ e) := rfl
  rw [h4] at h3
  rw [map_one] at h2
  have h5 : inclR R (e - σ e) * z = 0 := by
    rw [map_sub]; linear_combination h3 - inclR R (σ e) * h2
  exact (((IsUnit.mk0 _ (sub_ne_zero.2 he.symm)).map (inclR R)).mul_right_eq_zero).1 h5

theorem eq_zero_of_BR (h : IsCMExt F E σ) (hJ : IsHermND σ J) (x : Fin 1 → Fin M → R ⊗[F] E)
    (hx : ∀ y, BR R σ J x y = 0) : x = 0 := by
  classical
  have h1 : ∀ y, hR R σ J (x 0) y = 0 := fun y => eq_zero_of_trace R h _ fun c => by
    have := hx fun _ => c • y
    rwa [BR, Fin.sum_univ_one, hR_smul_right] at this
  have h2 : Matrix.vecMul (fun i => sigR R σ (x 0 i)) (JR R J) = 0 := by
    ext j
    have := h1 (Pi.single j 1)
    simpa [hR, Formalism.UG.hform, Pi.single_apply, Matrix.vecMul, dotProduct] using this
  have h3 : IsUnit (JR (F := F) R J).det := by
    have : (JR (F := F) R J).det = inclR (F := F) R J.det := (RingHom.map_det (inclR (F := F) R) J).symm
    rw [this]
    exact (IsUnit.mk0 _ hJ.2).map _
  have h4 : (fun i => sigR R σ (x 0 i)) = 0 := by
    have := congrArg (fun w => Matrix.vecMul w (JR (F := F) R J)⁻¹) h2
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ h3] using this
  ext a i
  rw [Subsingleton.elim a 0, ← sigR_sigR R h (x 0 i), congrFun h4 i]
  simp

end Form

theorem existsUnique_selfDual_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F), (∃! ν, SdR (Fv F v) (psiV F ψ v) ν) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃! μ, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 μ := by
  intro F E _ _ _ _ _ σ h ψ hψ v
  haveI := h.1
  let χ : AddChar (Fv F v) ℂ := ψ.compAddMonoidHom
    ((AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom)
  have hc : Continuous χ :=
    hψ.1.comp (Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v))
  have hu : ∀ t, ‖χ t‖ = 1 := fun t => hψ.2.1 _
  have hne : ∃ t, χ t ≠ 1 := (GlobalTheory.T.localComponents_nontrivial_adelic_character F ψ hψ).1 v
  refine ⟨existsUnique_of_bilin v χ hc hu hne (Fv F v) (LinearMap.mul _ _) (fun x y => mul_comm x y)
    (fun x hx => by simpa using hx 1), fun M J hJ => ?_⟩
  exact existsUnique_of_bilin v χ hc hu hne _ (bilin (Fv F v) σ J 1) (BR_symm _ h hJ) (eq_zero_of_BR _ h hJ)

end GlobalTheory.SelfDualFinite
