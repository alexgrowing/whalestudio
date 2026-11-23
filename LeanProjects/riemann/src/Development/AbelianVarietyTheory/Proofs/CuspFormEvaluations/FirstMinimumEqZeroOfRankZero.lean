import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bExpHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealFlowPeriodsSpanEqTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness

open NumberField Complex MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.FD
open scoped Pointwise

namespace GlobalTheory.FJZero

noncomputable def expo {Ψ : Type} [Fintype Ψ] (ν s : Ψ → ℝ) : ℂ :=
  cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ)

section General

variable {Ψ : Type} [Fintype Ψ]

theorem expo_eq (ν s : Ψ → ℝ) :
    expo ν s = cexp (((4 * Real.pi * ∑ τ, ν τ * s τ : ℝ) : ℂ) * I) := by
  unfold expo
  congr 1
  push_cast
  ring

theorem norm_expo (ν s : Ψ → ℝ) : ‖expo ν s‖ = 1 := by
  rw [expo_eq, Complex.norm_exp_ofReal_mul_I]

theorem expo_add (ν s t : Ψ → ℝ) : expo ν (s + t) = expo ν s * expo ν t := by
  unfold expo
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [mul_add]

theorem expo_nsmul (ν s : Ψ → ℝ) (k : ℕ) : expo ν (k • s) = expo ν s ^ k := by
  induction k with
  | zero => simp [expo]
  | succ k ih => rw [succ_nsmul, expo_add, ih, pow_succ]

theorem continuous_expo (ν : Ψ → ℝ) : Continuous (expo ν) := by
  unfold expo
  fun_prop

theorem exists_expo_ne_one {ι : Type*} [Countable ι] (ν : ι → Ψ → ℝ) :
    ∃ v : Ψ → ℝ, ∀ i, ν i ≠ 0 → expo (ν i) v ≠ 1 := by
  let φ : ι → (Ψ → ℝ) →ₗ[ℝ] ℝ := fun i =>
    { toFun := fun p => ∑ τ, ν i τ * p τ
      map_add' := fun p q => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c p => by simp [Finset.mul_sum, mul_left_comm] }
  have h1 : ∀ i, ∀ᵐ v : Ψ → ℝ, ν i ≠ 0 → φ i v ≠ 0 := by
    intro i
    by_cases hi : ν i = 0
    · exact Eventually.of_forall fun v h => absurd hi h
    have hne : LinearMap.ker (φ i) ≠ ⊤ := by
      intro htop
      have h0 : φ i (ν i) = 0 := by
        rw [← LinearMap.mem_ker, htop]
        exact Submodule.mem_top
      apply hi
      have hsq : ∑ τ, ν i τ ^ 2 = 0 := by simpa [φ, sq] using h0
      funext τ
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => sq_nonneg (ν i τ))).mp hsq τ
        (Finset.mem_univ τ)
      simpa using this
    have h0 := Measure.addHaar_submodule (volume : Measure (Ψ → ℝ)) _ hne
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with v hv _
    exact hv
  obtain ⟨v0, hv0⟩ := (ae_all_iff.mpr h1).exists
  have hc : (Set.range fun p : ι × ℤ => (p.2 : ℝ) / (2 * φ p.1 v0)).Countable :=
    Set.countable_range _
  obtain ⟨u, hu⟩ := hc.dense_compl ℝ |>.nonempty
  refine ⟨u • v0, fun i hi h => hu ?_⟩
  rw [expo_eq, Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨(i, k), ?_⟩
  have hφ := hv0 i hi
  have e : (∑ τ, ν i τ * (u • v0) τ) = u * φ i v0 := by
    simp [φ, Finset.mul_sum, mul_left_comm]
  rw [e] at hk
  have hk' : (4 * Real.pi * (u * φ i v0) : ℝ) = k * (2 * Real.pi) := by
    have h2 : (((4 * Real.pi * (u * φ i v0) : ℝ) : ℂ)) = ((k * (2 * Real.pi) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ I_ne_zero
      rw [hk]
      push_cast
      ring
    exact_mod_cast h2
  have hpi := Real.pi_pos
  show (k : ℝ) / (2 * φ i v0) = u
  rw [div_eq_iff (mul_ne_zero two_ne_zero hφ)]
  apply mul_right_cancel₀ (show (2 * Real.pi) ≠ 0 by positivity)
  rw [← hk']
  ring

theorem eq_zero_of_hasSum_pow {ι : Type*} (B z : ι → ℂ) (c : ℂ) (hB : Summable fun i => ‖B i‖)
    (hz : ∀ i, ‖z i‖ = 1) (hz1 : ∀ i, B i ≠ 0 → z i ≠ 1)
    (hs : ∀ k : ℕ, HasSum (fun i => B i * z i ^ k) c) : c = 0 := by
  let F : ℕ → ι → ℂ := fun N i => B i * (((N + 1 : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (N + 1), z i ^ k)
  have hF : ∀ N, ∑' i, F N i = c := by
    intro N
    have h := (hasSum_sum (s := Finset.range (N + 1)) fun k _ => hs k).mul_left
      (((N + 1 : ℕ) : ℂ)⁻¹)
    have hN : ((N + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero N)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN,
      one_mul] at h
    rw [← h.tsum_eq]
    refine tsum_congr fun i => ?_
    simp only [F]
    rw [← Finset.mul_sum]
    ring
  have hlim : Tendsto (fun N => ∑' i, F N i) atTop (𝓝 (∑' _ : ι, (0 : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence hB (fun i => ?_) (Eventually.of_forall fun N i => ?_)
    · by_cases hi : B i = 0
      · simp [F, hi]
      have h1 := hz1 i hi
      have hd : 0 < ‖z i - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have ht : Tendsto (fun N : ℕ => ‖B i‖ * (2 / ‖z i - 1‖) * (1 / ((N : ℝ) + 1))) atTop
          (𝓝 (‖B i‖ * (2 / ‖z i - 1‖) * 0)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
      rw [mul_zero] at ht
      refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) ht
      simp only [F]
      rw [geom_sum_eq h1, norm_mul, norm_mul, norm_inv, norm_div, Complex.norm_natCast]
      have h2 : ‖z i ^ (N + 1) - 1‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_pow, hz, one_pow, norm_one]
        norm_num
      push_cast
      rw [one_div, mul_assoc, mul_comm (2 / _)]
      gcongr
    · simp only [F]
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
      have h2 : ‖∑ k ∈ Finset.range (N + 1), z i ^ k‖ ≤ ((N + 1 : ℕ) : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        simp [norm_pow, hz]
      have h3 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      have h4 : ((N + 1 : ℕ) : ℝ)⁻¹ * ‖∑ k ∈ Finset.range (N + 1), z i ^ k‖ ≤ 1 := by
        rw [inv_mul_le_iff₀ h3, mul_one]
        exact h2
      exact mul_le_of_le_one_right (norm_nonneg _) h4
  simp only [hF, tsum_zero] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

theorem setIntegral_add_right (L : AddSubgroup (Ψ → ℝ)) [Countable L] {D : Set (Ψ → ℝ)}
    (hD : IsAddFundamentalDomain L D volume) (f : (Ψ → ℝ) → ℂ)
    (hper : ∀ p ∈ L, ∀ s, f (s + p) = f s) (t : Ψ → ℝ) :
    ∫ s in D, f (s + t) = ∫ s in D, f s := by
  have hD' : IsAddFundamentalDomain L (t +ᵥ D) volume := hD.vadd_of_comm t
  have h1 := hD.setIntegral_eq hD' (f := f) (fun g s => by
    show f ((g : Ψ → ℝ) + s) = f s
    rw [add_comm]
    exact hper g g.2 s)
  rw [h1]
  have h2 := (measurePreserving_add_left (volume : Measure (Ψ → ℝ)) t).setIntegral_image_emb
    (measurableEmbedding_addLeft t) f D
  have e : t +ᵥ D = (fun s => t + s) '' D := rfl
  rw [e, h2]
  simp only [add_comm]

theorem setIntegral_eq_zero (L : AddSubgroup (Ψ → ℝ)) [Countable L] {D : Set (Ψ → ℝ)}
    (hD : IsAddFundamentalDomain L D volume) (hfin : volume D < ⊤) (f : (Ψ → ℝ) → ℂ)
    (hper : ∀ p ∈ L, ∀ s, f (s + p) = f s) {ι : Type*} [Countable ι] (A : ι → ℂ)
    (hA : Summable fun i => ‖A i‖) (ν : ι → Ψ → ℝ)
    (hs : ∀ s, HasSum (fun i => A i * expo (ν i) s) (f s)) (hν : ∀ i, A i ≠ 0 → ν i ≠ 0) :
    ∫ s in D, f s = 0 := by
  haveI : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hfin⟩
  obtain ⟨v, hv⟩ := exists_expo_ne_one ν
  have hint : ∀ i (c : ℂ), Integrable (fun s => c * expo (ν i) s) (volume.restrict D) := fun i c =>
    Integrable.of_bound (continuous_const.mul (continuous_expo _)).aestronglyMeasurable ‖c‖
      (Eventually.of_forall fun s => by rw [norm_mul, norm_expo, mul_one])
  set V : ℝ := (volume.restrict D).real Set.univ with hV
  have hJ : ∀ i, ‖∫ s in D, expo (ν i) s‖ ≤ V := fun i => by
    have := norm_integral_le_of_norm_le_const (μ := volume.restrict D) (f := expo (ν i)) (C := 1)
      (Eventually.of_forall fun s => (norm_expo _ _).le)
    rwa [one_mul] at this
  refine eq_zero_of_hasSum_pow (fun i => A i * ∫ s in D, expo (ν i) s) (fun i => expo (ν i) v) _
    ?_ (fun i => norm_expo _ _) (fun i hi => hv i (hν i (left_ne_zero_of_mul hi))) fun k => ?_
  · refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) (hA.mul_right V)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hJ i) (norm_nonneg _)
  · rw [← setIntegral_add_right L hD f hper (k • v)]
    have h := hasSum_integral_of_summable_integral_norm (μ := volume.restrict D)
      (F := fun i s => (A i * expo (ν i) v ^ k) * expo (ν i) s) (fun i => hint i _) (by
        simp only [norm_mul, norm_pow, norm_expo, one_pow, mul_one, integral_const, smul_eq_mul]
        exact hA.mul_left _)
    have e1 : (fun i => ∫ s in D, A i * expo (ν i) v ^ k * expo (ν i) s) =
        fun i => (A i * ∫ s in D, expo (ν i) s) * expo (ν i) v ^ k := by
      funext i
      rw [integral_const_mul]
      ring
    have e2 : (fun s => ∑' i, A i * expo (ν i) v ^ k * expo (ν i) s) = fun s => f (s + k • v) := by
      funext s
      rw [← (hs (s + k • v)).tsum_eq]
      refine tsum_congr fun i => ?_
      rw [expo_add, expo_nsmul]
      ring
    rw [e1, e2] at h
    exact h

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem fj_eq_zero_of_hasSum_ne (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin r → E) (x : Frame X.Ψ r)
    (Q : Frame X.Ψ r → ℂ) {ι : Type*} [Countable ι] (A : ι → ℂ) (hA : Summable fun i => ‖A i‖)
    (ν : ι → X.Ψ → ℝ)
    (hs : ∀ s : X.Ψ → ℝ,
      HasSum (fun i => A i * cexp (4 * Real.pi * I * ∑ τ, (ν i τ : ℂ) * s τ))
        (Q (X.flow ξ (fun τ => (s τ : ℂ)) x)))
    (hper : ∀ p ∈ X.periods la, ∀ s : X.Ψ → ℝ,
      Q (X.flow ξ (fun τ => ((s + p) τ : ℂ)) x) = Q (X.flow ξ (fun τ => (s τ : ℂ)) x))
    (μ : X.Ψ → ℝ) (hν : ∀ i, A i ≠ 0 → ν i ≠ μ) : X.fj la ξ μ Q x = 0 := by
  haveI := PeriodLatticeCountable.periods_countable X la
  unfold Data.fj
  split_ifs with hf h
  · obtain ⟨-, hD, -, hfin⟩ := h.choose_spec
    have hexp : ∀ s : X.Ψ → ℝ,
        cexp (-(4 * Real.pi * I) * ∑ τ, (μ τ : ℂ) * s τ) = expo (-μ) s := by
      intro s
      unfold expo
      congr 1
      simp
    simp only [hexp]
    rw [setIntegral_eq_zero (X.periods la) hD hfin
      (fun s => Q (X.flow ξ (fun τ => (s τ : ℂ)) x) * expo (-μ) s) ?_ A hA (fun i => ν i - μ) ?_
      (fun i hi => sub_ne_zero.mpr (hν i hi)), mul_zero]
    · intro p hp s
      obtain ⟨k, hk⟩ := hf p hp
      have h1 : expo (-μ) p = 1 := by
        rw [expo_eq, Complex.exp_eq_one_iff]
        refine ⟨-k, ?_⟩
        have e : (4 * Real.pi * ∑ τ, (-μ) τ * p τ : ℝ) = -k * (2 * Real.pi) := by
          simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
          rw [← hk]
          ring
        rw [e]
        push_cast
        ring
      show Q (X.flow ξ (fun τ => ((s + p) τ : ℂ)) x) * expo (-μ) (s + p) = _
      rw [hper p hp s, expo_add, h1, mul_one]
    · intro s
      have h1 := (hs s).mul_right (expo (-μ) s)
      have e : (fun i => A i * cexp (4 * Real.pi * I * ∑ τ, (ν i τ : ℂ) * s τ) * expo (-μ) s) =
          fun i => A i * expo (ν i - μ) s := by
        funext i
        unfold expo
        rw [mul_assoc, ← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
        congr 3
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp only [Pi.neg_apply, Pi.sub_apply]
        push_cast
        ring
      rw [e] at h1
      exact h1
  · rfl
  · rfl

theorem fj_zero_of_hasSum (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin r → E) (x : Frame X.Ψ r)
    (Q : Frame X.Ψ r → ℂ) {ι : Type*} [Countable ι] (A : ι → ℂ) (hA : Summable fun i => ‖A i‖)
    (ν : ι → X.Ψ → ℝ)
    (hs : ∀ s : X.Ψ → ℝ,
      HasSum (fun i => A i * cexp (4 * Real.pi * I * ∑ τ, (ν i τ : ℂ) * s τ))
        (Q (X.flow ξ (fun τ => (s τ : ℂ)) x)))
    (hper : ∀ p ∈ X.periods la, ∀ s : X.Ψ → ℝ,
      Q (X.flow ξ (fun τ => ((s + p) τ : ℂ)) x) = Q (X.flow ξ (fun τ => (s τ : ℂ)) x))
    (hν : ∀ i, A i ≠ 0 → ν i ≠ 0) : X.fj la ξ 0 Q x = 0 :=
  fj_eq_zero_of_hasSum_ne X la ξ x Q A hA ν hs hper 0 hν

theorem firstMinimum_eq_zero_of_rank_zero (X : Data E 0) (x : Frame X.Ψ 0) : X.la1 x = 0 := by
  have h : {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨v, -, hv, -⟩
    exact hv (Subsingleton.elim _ _)
  unfold Data.la1 Data.firstMinimumSq
  rw [h, Real.sInf_empty, Real.sqrt_zero]

theorem firstMinimum_bounded_on_domain (X : Data E r) : ∃ B : ℝ, 0 < B ∧ ∀ x ∈ X.dom, X.la1 x ≤ B := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨1, one_pos, fun x _ => by rw [firstMinimum_eq_zero_of_rank_zero]; exact zero_le_one⟩
  obtain ⟨hinv, hcont, -⟩ := ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames r X hr
  obtain ⟨K, hK, hKd, hcov⟩ := FlagMahler.mahler_compactness r X 1 one_pos
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn (hcont.mono hKd)).bddAbove
  refine ⟨max B 1, lt_max_of_lt_right one_pos, fun x hx => ?_⟩
  rcases le_total 1 (X.la1 x) with h | h
  · obtain ⟨γ, hγ, b, hb, hmem⟩ := hcov x hx h
    rw [← hinv γ hγ x hx b hb]
    exact le_max_of_le_left (hB ⟨_, hmem, rfl⟩)
  · exact le_max_of_le_right h

theorem rpow_mul_exp_neg_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → u ^ a * Real.exp (-b * u) ≤ M := by
  refine ⟨((a + 1) / b) ^ a, fun u hu => ?_⟩
  have h1 : u ≤ (a + 1) / b * Real.exp (b * u / (a + 1)) := by
    have h := Real.add_one_le_exp (b * u / (a + 1))
    calc u = (a + 1) / b * (b * u / (a + 1)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : u ^ a ≤ ((a + 1) / b) ^ a * Real.exp (b * u / (a + 1) * a) := by
    rw [Real.exp_mul, ← Real.mul_rpow (by positivity) (Real.exp_pos _).le]
    exact Real.rpow_le_rpow hu h1 ha
  have h3 : Real.exp (b * u / (a + 1) * a) * Real.exp (-b * u) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    have : b * u / (a + 1) * a ≤ b * u := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hb.le hu]
    linarith
  calc u ^ a * Real.exp (-b * u)
      ≤ ((a + 1) / b) ^ a * Real.exp (b * u / (a + 1) * a) * Real.exp (-b * u) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = ((a + 1) / b) ^ a * (Real.exp (b * u / (a + 1) * a) * Real.exp (-b * u)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) h3

theorem fj_eq_zero_of_isSec (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (hsec : X.IsSec la Q) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {ι : Type*} [Countable ι] (A : ι → ℂ) (hA : Summable fun i => ‖A i‖) (ν : ι → X.Ψ → ℝ)
    (hs : ∀ s : X.Ψ → ℝ,
      HasSum (fun i => A i * cexp (4 * Real.pi * I * ∑ τ, (ν i τ : ℂ) * s τ))
        (Q (X.flow ξ (fun τ => (s τ : ℂ)) x)))
    (μ : X.Ψ → ℝ) (hν : ∀ i, A i ≠ 0 → ν i ≠ μ) : X.fj la ξ μ Q x = 0 := by
  refine fj_eq_zero_of_hasSum_ne X la ξ x Q A hA ν hs (fun p hp s => ?_) μ hν
  have h1 : X.flow ξ (fun τ => ((s + p) τ : ℂ)) x =
      X.flow ξ (TransvectionPeriodicity.cR X p) (X.flow ξ (TransvectionPeriodicity.cR X s) x) := by
    rw [EmbeddingHermitianPairs.flow_flow X hξ.2.1, ← TransvectionPeriodicity.cR_add, add_comm s p]
    rfl
  rw [h1, TransvectionPeriodicity.sec_periodic X la Q hsec hξ.1 hξ.2.1 hp _
    (TransvectionPeriodicity.flow_real_mem_dom X hξ.2.1 s x hx)]
  rfl

theorem bounded_of_moderate_nonneg (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    (hsec : X.IsSec la P) (C A : ℝ) (hA0 : 0 ≤ A)
    (hmod : ∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-A))
    (hcusp : ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, X.fj la ξ 0 P x = 0) :
    ∃ B : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ B := by
  classical
  obtain ⟨hnn, hdec⟩ := moderateCoefficientPositivity_holds r X la P C A hsec hmod
  obtain ⟨Cη, hCη⟩ := hdec (1 / 2) (by norm_num) (by norm_num)
  set N : ℕ := X.m * X.chiOrd la with hNdef
  have hN : 0 < N := Nat.mul_pos X.m_pos (X.χ_fin la).choose_spec.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : (fun τ : X.Ψ => ((N : ℕ) : ℝ) * (τ.1 (1 : E)).re) ∈ X.periods la :=
    AddSubgroup.subset_closure ⟨1, by simp [cc], isIntegral_one, rfl⟩
  set c' : ℝ := 1 / (2 * N) with hc'
  have hc'0 : 0 < c' := by positivity
  have hsupp : ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ ν, X.fj la ξ ν P x ≠ 0 →
      FrequencySumBounds.IsFreq X la ν ∧ c' ≤ ∑ τ, ν τ := by
    intro ξ hξ x hx ν hne
    have h0 := hnn ξ hξ ν x hx hne
    have hfreq : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k := by
      by_contra hf
      apply hne
      unfold Data.fj
      rw [if_neg hf]
    refine ⟨⟨h0, hfreq⟩, ?_⟩
    have hgt : 0 < ∑ τ, ν τ := by
      refine lt_of_le_of_ne (Finset.sum_nonneg fun τ _ => h0 τ) fun hz => hne ?_
      have : ν = 0 := funext fun τ =>
        (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => h0 τ).mp hz.symm τ (Finset.mem_univ τ)
      rw [this]
      exact hcusp ξ hξ x hx
    obtain ⟨k, hk⟩ := hfreq _ hp0
    have e : 2 * (N : ℝ) * ∑ τ, ν τ = k := by
      rw [← hk, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp
      ring
    have hk0 : (0 : ℝ) < k := by rw [← e]; positivity
    have hk1 : (1 : ℝ) ≤ k := by
      have : 0 < k := by exact_mod_cast hk0
      exact_mod_cast this
    rw [hc', div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨K, hK⟩ := FrequencySumBounds.freq_sum_bound X la (2 * Real.pi) (by positivity)
  have hK0 : 0 ≤ K := by
    have := hK ∅ (by simp)
    simpa using this
  obtain ⟨δ0, hδ0, hiso⟩ := IsotropicThreshold.iso_threshold X
  obtain ⟨M, hM⟩ := rpow_mul_exp_neg_le (A / 2) (Real.pi * c') (by positivity) (by positivity)
  set ε : ℝ := min (δ0 / 2) (1 / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by norm_num)
  refine ⟨max (max |C| (|C| * Real.sqrt ε ^ (-A)))
    (|Cη| * M * Real.exp (2 * Real.pi * c') * K), fun x hx => ?_⟩
  have hla0 : 0 ≤ X.firstMinimumSq x := MinimumGrowthBounds.minimumSq_nonneg X hx
  have hl0 : 0 ≤ X.la1 x ^ (-A) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hmod' : X.pnorm la P x ≤ |C| * X.la1 x ^ (-A) :=
    (hmod x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hl0)
  have hnf0 : 0 < X.nfac la x := MinimumGrowthBounds.nfac_pos X la hx
  have hpn : X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
  rcases lt_or_ge (X.firstMinimumSq x) ε with hsmall | hbig
  · rcases eq_or_lt_of_le hla0 with h0 | hpos
    · refine le_max_of_le_left (le_max_of_le_left (hmod'.trans ?_))
      have : X.la1 x = 0 := by unfold Data.la1; rw [← h0, Real.sqrt_zero]
      rw [this]
      exact mul_le_of_le_one_right (abs_nonneg C) (Real.zero_rpow_le_one _)
    refine le_max_of_le_right ?_
    set L := X.firstMinimumSq x with hL
    have hTne : {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have : L = 0 := by
        show sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)} = 0
        rw [hempty, Real.sInf_empty]
      linarith
    have hlt : sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)} < 2 * L := by
      show L < 2 * L
      linarith
    obtain ⟨t, ⟨v, hvΛ, hv0, rfl⟩, ht⟩ := exists_lt_of_csInf_lt hTne hlt
    have hεδ : ε ≤ δ0 / 2 := min_le_left _ _
    have hε1 : ε ≤ 1 / 2 := min_le_right _ _
    have hvv : herm X.Gm v v = 0 := hiso x hx v hvΛ (by linarith)
    have hξ : X.IsIso v := ⟨hvΛ, hvv, hv0⟩
    have hterm : ∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) ≤
        ∑ τ', X.c τ' * X.maj x τ' (Data.emb τ'.1 v) := fun τ =>
      Finset.single_le_sum (f := fun τ' : X.Ψ => X.c τ' * X.maj x τ' (Data.emb τ'.1 v))
        (fun τ' _ => mul_nonneg (IsotropicThreshold.c_pos X τ').le (MajorantOperators.maj_nonneg hx τ' _))
        (Finset.mem_univ τ)
    have htpos : ∀ τ, 0 < X.c τ * X.maj x τ (Data.emb τ.1 v) := fun τ =>
      mul_pos (IsotropicThreshold.c_pos X τ) (X.maj_pos hx τ (emb_ne_zero τ.1 hv0))
    have hcond : ∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) ≤ 1 := fun τ => by
      have := hterm τ
      linarith
    set t0 : ℝ := 1 / (2 * L) with ht0
    have ht01 : 1 ≤ t0 := by
      rw [ht0, le_div_iff₀ (by positivity)]
      linarith
    have htt : ∀ τ, t0 ≤ X.tt v x τ := by
      intro τ
      show t0 ≤ 1 / (X.c τ * X.maj x τ (Data.emb τ.1 v))
      rw [ht0]
      exact one_div_le_one_div_of_le (htpos τ) (by have := hterm τ; linarith)
    have hsum : HasSum (fun ν => X.fj la v ν P x) (P x) := by
      have h := m3bExp_holds r X la P hsec v hξ x hx 0 (by rw [EmbeddingHermitianPairs.flow_zero]; exact hx)
      simpa [EmbeddingHermitianPairs.flow_zero] using h
    have hpow : X.la1 x ^ (-A) * Real.exp (-2 * Real.pi * t0 * c') ≤ M := by
      have h1 : X.la1 x ^ (-A) = L⁻¹ ^ (A / 2) := by
        show Real.sqrt L ^ (-A) = _
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le, Real.inv_rpow hpos.le,
          ← Real.rpow_neg hpos.le]
        congr 1
        ring
      have h2 : -2 * Real.pi * t0 * c' = -(Real.pi * c') * L⁻¹ := by
        rw [ht0]
        field_simp
      rw [h1, h2]
      exact hM _ (by positivity)
    have hM0 : 0 ≤ M := le_trans (by positivity) hpow
    set D : ℝ := |Cη| * M * Real.exp (2 * Real.pi * c') with hD
    have hD0 : 0 ≤ D := by positivity
    have hterm_bd : ∀ ν, X.fj la v ν P x ≠ 0 → ‖X.fj la v ν P x‖ * X.nfac la x ≤
        D * Real.exp (-(2 * Real.pi) * ∑ τ, ν τ) := by
      intro ν hne
      obtain ⟨⟨hν0, -⟩, hνc⟩ := hsupp v hξ x hx ν hne
      have h1 := hCη v hξ ν x hx hcond
      have hA : t0 * ∑ τ, ν τ ≤ ∑ τ, ν τ * X.tt v x τ := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun τ _ => ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (htt τ) (hν0 τ)
      have hB : t0 * c' + (∑ τ, ν τ) - c' ≤ ∑ τ, ν τ * X.tt v x τ := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ht01) (sub_nonneg.mpr hνc)]
      have hexp : Real.exp (-4 * Real.pi * (1 - 1 / 2) * ∑ τ, ν τ * X.tt v x τ) ≤
          Real.exp (-2 * Real.pi * t0 * c') * Real.exp (2 * Real.pi * c') *
            Real.exp (-(2 * Real.pi) * ∑ τ, ν τ) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos]
      calc ‖X.fj la v ν P x‖ * X.nfac la x
          ≤ Cη * X.la1 x ^ (-A) *
              Real.exp (-4 * Real.pi * (1 - 1 / 2) * ∑ τ, ν τ * X.tt v x τ) := h1
        _ ≤ |Cη| * X.la1 x ^ (-A) * (Real.exp (-2 * Real.pi * t0 * c') *
              Real.exp (2 * Real.pi * c') * Real.exp (-(2 * Real.pi) * ∑ τ, ν τ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hl0) hexp (Real.exp_pos _).le
              (by positivity)
        _ = |Cη| * (X.la1 x ^ (-A) * Real.exp (-2 * Real.pi * t0 * c')) *
              Real.exp (2 * Real.pi * c') * Real.exp (-(2 * Real.pi) * ∑ τ, ν τ) := by ring
        _ ≤ _ := by rw [hD]; gcongr
    have hfs : ∀ F : Finset (X.Ψ → ℝ), ∑ ν ∈ F, ‖X.fj la v ν P x‖ * X.nfac la x ≤ D * K := by
      intro F
      rw [← Finset.sum_filter_of_ne (p := fun ν => X.fj la v ν P x ≠ 0) (fun ν _ hfν => by
        intro hfj
        apply hfν
        rw [hfj, norm_zero, zero_mul])]
      calc ∑ ν ∈ F.filter (fun ν => X.fj la v ν P x ≠ 0), ‖X.fj la v ν P x‖ * X.nfac la x
          ≤ ∑ ν ∈ F.filter (fun ν => X.fj la v ν P x ≠ 0),
              D * Real.exp (-(2 * Real.pi) * ∑ τ, ν τ) :=
            Finset.sum_le_sum fun ν hν => hterm_bd ν (Finset.mem_filter.mp hν).2
        _ = D * ∑ ν ∈ F.filter (fun ν => X.fj la v ν P x ≠ 0),
              Real.exp (-(2 * Real.pi) * ∑ τ, ν τ) := by
            rw [Finset.mul_sum]
        _ ≤ D * K := by
            apply mul_le_mul_of_nonneg_left _ hD0
            exact hK _ fun ν hν => (hsupp v hξ x hx ν (Finset.mem_filter.mp hν).2).1
    have hne' := hnf0.ne'
    have hsf : Summable (fun ν => ‖X.fj la v ν P x‖ * X.nfac la x) :=
      summable_of_sum_le (fun ν => by positivity) hfs
    have hsn : Summable (fun ν => ‖X.fj la v ν P x‖) :=
      (hsf.div_const (X.nfac la x)).congr (fun ν => by field_simp)
    calc X.pnorm la P x = ‖∑' ν, X.fj la v ν P x‖ * X.nfac la x := by rw [hsum.tsum_eq, hpn]
      _ ≤ (∑' ν, ‖X.fj la v ν P x‖) * X.nfac la x :=
          mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsn) hnf0.le
      _ = ∑' ν, ‖X.fj la v ν P x‖ * X.nfac la x := tsum_mul_right.symm
      _ ≤ D * K := Real.tsum_le_of_sum_le (fun ν => by positivity) hfs
  · refine le_max_of_le_left (le_max_of_le_right (hmod'.trans ?_))
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    exact Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.mpr hε0) (Real.sqrt_le_sqrt hbig)
      (by linarith)

theorem mem_SS_of_isModerate (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (hsec : X.IsSec la Q) (hmod : X.IsModerate la Q)
    (hcusp : ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, X.fj la ξ 0 Q x = 0) : Q ∈ X.SS la := by
  obtain ⟨C, A, hC⟩ := hmod
  refine ⟨⟨hsec, ?_⟩, hcusp⟩
  rcases le_total 0 A with hA | hA
  · exact bounded_of_moderate_nonneg X la Q hsec C A hA hC hcusp
  obtain ⟨B, -, hB⟩ := firstMinimum_bounded_on_domain X
  refine ⟨|C| * B ^ (-A), fun x hx => (hC x hx).trans ?_⟩
  have hl : 0 ≤ X.la1 x := Real.sqrt_nonneg _
  exact mul_le_mul (le_abs_self C) (Real.rpow_le_rpow hl (hB x hx) (by linarith))
    (Real.rpow_nonneg hl _) (abs_nonneg C)

theorem isModerate_of_le_one_add_inv (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (C A : ℝ) (hC : ∀ x ∈ X.dom, X.pnorm la Q x ≤ C * (1 + 1 / X.la1 x) ^ A) :
    X.IsModerate la Q := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨C, 0, fun x hx => ?_⟩
    simpa [firstMinimum_eq_zero_of_rank_zero] using hC x hx
  obtain ⟨-, -, hpos⟩ := ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames r X hr
  obtain ⟨B, hB0, hB⟩ := firstMinimum_bounded_on_domain X
  refine ⟨|C| * (B + 1) ^ |A|, |A|, fun x hx => (hC x hx).trans ?_⟩
  have hl := hpos x hx
  have h1 : 1 ≤ 1 + 1 / X.la1 x := le_add_of_nonneg_right (by positivity)
  have h2 : (1 + 1 / X.la1 x) ^ A ≤ (B + 1) ^ |A| * X.la1 x ^ (-|A|) := by
    refine (Real.rpow_le_rpow_of_exponent_le h1 (le_abs_self A)).trans ?_
    rw [Real.rpow_neg hl.le, ← Real.inv_rpow hl.le, ← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ (abs_nonneg A)
    have e : 1 + 1 / X.la1 x = (X.la1 x + 1) * (X.la1 x)⁻¹ := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith [hB x hx]) (by positivity)
  rw [mul_assoc]
  exact mul_le_mul (le_abs_self C) h2 (by positivity) (abs_nonneg C)

theorem mem_SS_of_le_one_add_inv (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (hsec : X.IsSec la Q) (C A : ℝ)
    (hC : ∀ x ∈ X.dom, X.pnorm la Q x ≤ C * (1 + 1 / X.la1 x) ^ A)
    (hcusp : ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, X.fj la ξ 0 Q x = 0) : Q ∈ X.SS la :=
  mem_SS_of_isModerate X la Q hsec (isModerate_of_le_one_add_inv X la Q C A hC) hcusp

theorem decay_of_isModerate (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (hsec : X.IsSec la Q) (hmod : X.IsModerate la Q)
    (hcusp : ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, X.fj la ξ 0 Q x = 0) :
    ∃ c C : ℝ, 0 < c ∧ Q ∈ X.SSgt la c ∧
      ∀ x ∈ X.dom, X.pnorm la Q x ^ 2 ≤ C * Real.exp (-2 * Real.pi * c / X.firstMinimumSq x) := by
  obtain ⟨c, hc, hQ⟩ := spectralGap_holds r X la Q (mem_SS_of_isModerate X la Q hsec hmod hcusp)
  obtain ⟨C, hC⟩ := cuspidalDecay_holds r X la Q c hc.le hQ
  exact ⟨c, C, hc, hQ, hC⟩

theorem main (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ) :
    (∀ (ξ : Fin r → E) (x : Frame X.Ψ r) (ι : Type) [Countable ι] (A : ι → ℂ)
      (ν : ι → X.Ψ → ℝ), (Summable fun i => ‖A i‖) →
      (∀ s : X.Ψ → ℝ, HasSum (fun i => A i * cexp (4 * Real.pi * I * ∑ τ, (ν i τ : ℂ) * s τ))
        (Q (X.flow ξ (fun τ => (s τ : ℂ)) x))) →
      (∀ p ∈ X.periods la, ∀ s : X.Ψ → ℝ,
        Q (X.flow ξ (fun τ => ((s + p) τ : ℂ)) x) = Q (X.flow ξ (fun τ => (s τ : ℂ)) x)) →
      (∀ i, A i ≠ 0 → ν i ≠ 0) → X.fj la ξ 0 Q x = 0) ∧
    (X.IsSec la Q → (∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, X.fj la ξ 0 Q x = 0) →
      (X.IsModerate la Q ∨
        ∃ C A : ℝ, ∀ x ∈ X.dom, X.pnorm la Q x ≤ C * (1 + 1 / X.la1 x) ^ A) → Q ∈ X.SS la) :=
  ⟨fun ξ x _ _ A ν hA hs hper hν => fj_zero_of_hasSum X la ξ x Q A hA ν hs hper hν,
    fun hsec hcusp h => h.elim (fun hm => mem_SS_of_isModerate X la Q hsec hm hcusp)
      fun ⟨C, A, hC⟩ => mem_SS_of_le_one_add_inv X la Q hsec C A hC hcusp⟩

end GlobalTheory.FJZero
