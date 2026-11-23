import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnAbsDetRpowLeOneFundamentalDomain

noncomputable section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open GlobalTheory.CuspRep.CuspidalL2GL
open scoped nonZeroDivisors ENNReal

namespace GlobalTheory.RSThetaRes

def lowSum (T s t : ℝ) : ℝ := ∑' n : ℤ, if T ^ n * t ≤ 1 then (T ^ n * t) ^ s else 0

theorem hasSum_lowSum {L s t : ℝ} (hL : 0 < L) (hs : 0 < s) (ht : 0 < t) :
    ∃ u : ℝ, Real.exp (-L) < u ∧ u ≤ 1 ∧
      HasSum (fun n : ℤ => if Real.exp L ^ n * t ≤ 1 then (Real.exp L ^ n * t) ^ s else 0)
        (u ^ s * (1 - Real.exp (-(s * L)))⁻¹) := by
  have hT : 1 < Real.exp L := Real.one_lt_exp_iff.2 hL
  have hT0 : 0 < Real.exp L := Real.exp_pos L
  obtain ⟨m, h1, h2⟩ := exists_mem_Ico_zpow (inv_pos.2 ht) hT
  have hm : ∀ n : ℤ, Real.exp L ^ n * t ≤ 1 ↔ n ≤ m := by
    intro n
    constructor
    · intro hn
      by_contra hc
      push_neg at hc
      have h3 : Real.exp L ^ (m + 1) ≤ Real.exp L ^ n := zpow_le_zpow_right₀ hT.le (by omega)
      have h4 : t⁻¹ < Real.exp L ^ n := h2.trans_le h3
      have h5 := mul_lt_mul_of_pos_right h4 ht
      rw [inv_mul_cancel₀ ht.ne'] at h5
      linarith
    · intro hn
      have h3 : Real.exp L ^ n ≤ t⁻¹ := (zpow_le_zpow_right₀ hT.le hn).trans h1
      calc Real.exp L ^ n * t ≤ t⁻¹ * t := mul_le_mul_of_nonneg_right h3 ht.le
        _ = 1 := inv_mul_cancel₀ ht.ne'
  refine ⟨Real.exp L ^ m * t, ?_, (hm m).2 le_rfl, ?_⟩
  · have h3 : t⁻¹ < Real.exp L ^ m * Real.exp L := by rwa [zpow_add_one₀ hT0.ne'] at h2
    have h4 : 1 < Real.exp L ^ m * t * Real.exp L := by
      have h5 := mul_lt_mul_of_pos_right h3 ht
      rw [inv_mul_cancel₀ ht.ne'] at h5
      linarith
    rw [Real.exp_neg]
    calc (Real.exp L)⁻¹ = (Real.exp L)⁻¹ * 1 := (mul_one _).symm
      _ < (Real.exp L)⁻¹ * (Real.exp L ^ m * t * Real.exp L) := mul_lt_mul_of_pos_left h4 (inv_pos.2 hT0)
      _ = Real.exp L ^ m * t := by field_simp
  · have hq0 : 0 ≤ Real.exp (-(s * L)) := (Real.exp_pos _).le
    have hq1 : Real.exp (-(s * L)) < 1 := by simpa using Real.exp_lt_exp.2 (neg_lt_zero.2 (mul_pos hs hL))
    have hg : Function.Injective (fun k : ℕ => m - (k : ℤ)) := fun i j h => by simpa using h
    rw [← hg.hasSum_iff]
    · have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((Real.exp L ^ m * t) ^ s)
      have hfun : ((fun n : ℤ => if Real.exp L ^ n * t ≤ 1 then (Real.exp L ^ n * t) ^ s else 0) ∘
          fun k : ℕ => m - (k : ℤ)) = fun i : ℕ => (Real.exp L ^ m * t) ^ s * Real.exp (-(s * L)) ^ i := by
        funext k
        simp only [Function.comp_apply]
        rw [if_pos ((hm _).2 (by omega)), zpow_sub₀ hT0.ne', zpow_natCast]
        have hk : Real.exp L ^ m / Real.exp L ^ k * t = (Real.exp L ^ m * t) * (Real.exp L ^ k)⁻¹ := by
          field_simp
        rw [hk, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity)]
        congr 1
        rw [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_nat_mul, ← Real.exp_neg]
        congr 1
        ring
      rw [hfun]
      exact this
    · intro n hn
      have hnm : ¬ n ≤ m := fun h => hn ⟨(m - n).toNat, by simp only; omega⟩
      rw [if_neg (fun h => hnm ((hm n).1 h))]

theorem lowSum_bounds {L s u : ℝ} (hL : 0 < L) (hs : 0 < s) (hu : Real.exp (-L) < u) (hu1 : u ≤ 1) :
    Real.exp (-(s * L)) / L ≤ s * (u ^ s * (1 - Real.exp (-(s * L)))⁻¹) ∧
      s * (u ^ s * (1 - Real.exp (-(s * L)))⁻¹) ≤ Real.exp (s * L) / L := by
  have hu0 : 0 < u := (Real.exp_pos _).trans hu
  have hy0 : 0 < s * L := mul_pos hs hL
  have hv1 : u ^ s ≤ 1 := Real.rpow_le_one hu0.le hu1 hs.le
  have hv0 : Real.exp (-(s * L)) < u ^ s := by
    have h := Real.rpow_lt_rpow (Real.exp_pos _).le hu hs
    rwa [← Real.exp_mul, neg_mul, mul_comm L s] at h
  have hD : 0 < 1 - Real.exp (-(s * L)) := by linarith
  have hDy : 1 - Real.exp (-(s * L)) ≤ s * L := by have := Real.add_one_le_exp (-(s * L)); linarith
  have hE : Real.exp (s * L) * Real.exp (-(s * L)) = 1 := by rw [← Real.exp_add]; simp
  have hey : s * L + 1 ≤ Real.exp (s * L) := Real.add_one_le_exp _
  have hre : s * (u ^ s * (1 - Real.exp (-(s * L)))⁻¹) = s * u ^ s / (1 - Real.exp (-(s * L))) := by
    field_simp
  rw [hre]
  have hsv : s * u ^ s * L = u ^ s * (s * L) := by ring
  constructor
  · rw [div_le_div_iff₀ hL hD, hsv]
    nlinarith [mul_le_mul_of_nonneg_left hDy (Real.exp_pos (-(s * L))).le,
      mul_le_mul_of_nonneg_right hv0.le hy0.le]
  · rw [div_le_div_iff₀ hD hL, hsv]
    nlinarith [mul_le_mul_of_nonneg_right hv1 hy0.le]

theorem tendsto_mul_lowSum {L t : ℝ} (hL : 0 < L) (ht : 0 < t) :
    Tendsto (fun s : ℝ => s * lowSum (Real.exp L) s t) (𝓝[>] 0) (𝓝 (1 / L)) := by
  have hb : ∀ s : ℝ, 0 < s → Real.exp (-(s * L)) / L ≤ s * lowSum (Real.exp L) s t ∧
      s * lowSum (Real.exp L) s t ≤ Real.exp (s * L) / L := by
    intro s hs
    obtain ⟨u, hu, hu1, hsum⟩ := hasSum_lowSum hL hs ht
    rw [lowSum, hsum.tsum_eq]
    exact lowSum_bounds hL hs hu hu1
  have hlo : Tendsto (fun s : ℝ => Real.exp (-(s * L)) / L) (𝓝[>] 0) (𝓝 (1 / L)) := by
    have hc : Continuous fun s : ℝ => Real.exp (-(s * L)) / L := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun s : ℝ => Real.exp (s * L) / L) (𝓝[>] 0) (𝓝 (1 / L)) := by
    have hc : Continuous fun s : ℝ => Real.exp (s * L) / L := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs using (hb s hs).1
  · filter_upwards [self_mem_nhdsWithin] with s hs using (hb s hs).2

end GlobalTheory.RSThetaRes

namespace GlobalTheory.RSThetaRes

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem tendsto_residue (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] {𝓕 𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) (h𝓕' : IsFundamentalDomain (latticeGL E a) 𝓕' μ)
    {F : GA E a → ℂ} (hF : Continuous F) {C : ℝ} (hC : ∀ g, ‖F g‖ ≤ C)
    (hinv : ∀ γ ∈ latticeGL E a, ∀ g, F (γ * g) = F g) :
    Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
      F g * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1 : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1)
      (𝓝 ((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ) * ∫ g in 𝓕', F g ∂μ)) := by
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  set L : ℝ := (a : ℝ) * (Module.finrank ℚ E : ℝ) with hLdef
  have hd0 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  have hL : 0 < L := mul_pos (Nat.cast_pos.2 ha) hd0
  have hTL : Real.exp 1 ^ (a * Module.finrank ℚ E) = Real.exp L := by
    rw [Real.exp_one_pow, hLdef]
    push_cast
    rfl
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = Real.exp L ^ n * δ g := fun n g => by
    rw [← hTL]; exact GlobalTheory.RSTheta.absDet_zpow_mul n g
  have hT1 : 1 < Real.exp L := Real.one_lt_exp_iff.2 hL
  have hm : MeasurableSet {g | δ g ≤ 1} := (isClosed_le hδc continuous_const).measurableSet
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  let φ : (ratGL E a).range × ℤ → latticeGL E a := fun p =>
    ⟨p.1 * splitCentre E a 1 ^ p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (zpow_mem_latticeGL _)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨_, γ, rfl⟩, n⟩ ⟨⟨_, γ', rfl⟩, n'⟩ h
      have h1 : ratGL E a γ * splitCentre E a 1 ^ n = ratGL E a γ' * splitCentre E a 1 ^ n' := congrArg Subtype.val h
      have h2 := congrArg (fun x => δ (x * 1)) h1
      simp only [mul_assoc, hδr, hδz] at h2
      obtain rfl : n = n' := zpow_right_injective₀ (one_pos.trans hT1) hT1.ne' (mul_right_cancel₀ (hδ0 1).ne' h2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h1)) rfl
    · rintro ⟨g, hg⟩
      obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
      exact ⟨⟨⟨_, γ, rfl⟩, n⟩, rfl⟩
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hμ' : μ 𝓕' < ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕']; exact measure_lt_top _ _

  have key : ∀ s : ℝ, 0 < s →
      IntegrableOn (fun g => F g * ((lowSum (Real.exp L) s (δ g) : ℝ) : ℂ)) 𝓕' μ ∧
      ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, F g * ((δ g ^ s : ℝ) : ℂ) ∂μ =
        ∫ g in 𝓕', F g * ((lowSum (Real.exp L) s (δ g) : ℝ) : ℂ) ∂μ := by
    intro s hs
    set f : GA E a → ℂ := {g | δ g ≤ 1}.indicator (fun g => F g * ((δ g ^ s : ℝ) : ℂ)) with hf
    have hsum : ∀ g, ∑' n : ℤ, f (splitCentre E a 1 ^ n * g) = F g * ((lowSum (Real.exp L) s (δ g) : ℝ) : ℂ) := by
      intro g
      rw [lowSum, Complex.ofReal_tsum, ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      simp only [hf, Set.indicator_apply, Set.mem_setOf_eq, hδz, hinv _ (zpow_mem_latticeGL n)]
      split_ifs <;> simp
    have hfm : AEStronglyMeasurable f μ :=
      ((hF.mul (Complex.continuous_ofReal.comp (hδc.rpow_const fun g => Or.inl (hδ0 g).ne'))).aestronglyMeasurable).indicator hm
    have hfin : ∫⁻ g in 𝓕', ∑' n : ℤ, ‖f (splitCentre E a 1 ^ n * g)‖ₑ ∂μ ≠ ⊤ := by
      obtain ⟨B, hB, hBle⟩ := GlobalTheory.RSThetaLow.exists_tsum_zpow_le_low hT1 hs
      have hpt : ∀ g, ∑' n : ℤ, ‖f (splitCentre E a 1 ^ n * g)‖ₑ ≤ ENNReal.ofReal C * B := by
        intro g
        refine le_trans ?_ (mul_le_mul_of_nonneg_left (hBle _ (hδ0 g)) zero_le)
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun n => ?_
        simp only [hf, Set.indicator_apply, Set.mem_setOf_eq, hδz, hinv _ (zpow_mem_latticeGL n)]
        split_ifs with h
        · have hp : 0 ≤ (Real.exp L ^ n * δ g) ^ s := Real.rpow_nonneg (mul_pos (zpow_pos (Real.exp_pos L) n) (hδ0 g)).le _
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hC0]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
          exact mul_le_mul_of_nonneg_right (hC g) hp
        · simp
      refine (lt_of_le_of_lt (lintegral_mono hpt) ?_).ne
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB.lt_top) hμ'
    obtain ⟨-, hI, -, heq⟩ := GlobalTheory.ThetaUnfold.integral_unfold μ (latticeGL E a) (ratGL E a).range
      (fun n : ℤ => splitCentre E a 1 ^ n) (Equiv.ofBijective φ hφ) (fun _ => rfl) h𝓕' h𝓕 f
      (by
        rintro _ ⟨γ, rfl⟩ g
        simp only [hf, Set.indicator_apply, Set.mem_setOf_eq, hδr, hinv _ (ratGL_mem_latticeGL γ)])
      hfm hfin
    refine ⟨?_, ?_⟩
    · exact Integrable.congr hI (ae_of_all _ hsum)
    · calc ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, F g * ((δ g ^ s : ℝ) : ℂ) ∂μ = ∫ g in 𝓕, f g ∂μ := by
            rw [hf, integral_indicator hm, Measure.restrict_restrict hm, Set.inter_comm]
        _ = _ := by rw [← heq]; exact integral_congr_ae (.of_forall hsum)

  have hlim0 : Tendsto (fun s : ℝ => ((s : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, F g * ((δ g ^ s : ℝ) : ℂ) ∂μ)
      (𝓝[>] 0) (𝓝 (((1 / L : ℝ) : ℂ) * ∫ g in 𝓕', F g ∂μ)) := by
    have hev : (fun s : ℝ => ((s : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g | δ g ≤ 1}, F g * ((δ g ^ s : ℝ) : ℂ) ∂μ) =ᶠ[𝓝[>] 0]
        fun s => ∫ g in 𝓕', F g * ((s * lowSum (Real.exp L) s (δ g) : ℝ) : ℂ) ∂μ := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [(key s hs).2, ← integral_const_mul]
      refine integral_congr_ae (.of_forall fun g => ?_)
      simp only
      push_cast
      ring
    rw [mul_comm, ← integral_mul_const]
    refine Tendsto.congr' hev.symm ?_
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C * (Real.exp L / L)) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine (((key s hs).1.const_mul (s : ℂ)).aestronglyMeasurable).congr (.of_forall fun g => ?_)
      simp only
      push_cast
      ring
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT one_pos] with s hs hs1
      refine .of_forall fun g => ?_
      obtain ⟨u, hu, hu1, hsum⟩ := hasSum_lowSum hL hs (hδ0 g)
      have hb := lowSum_bounds hL hs hu hu1
      rw [← hsum.tsum_eq, ← lowSum] at hb
      have hnn : 0 ≤ s * lowSum (Real.exp L) s (δ g) := (div_nonneg (Real.exp_pos _).le hL.le).trans hb.1
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
      refine mul_le_mul (hC g) (hb.2.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) hL.le)) hnn hC0
      have := hs1.2
      nlinarith
    · exact integrableOn_const hμ'.ne
    · refine .of_forall fun g => ?_
      exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp (tendsto_mul_lowSum hL (hδ0 g)))
  have hsub : Tendsto (fun x : ℝ => x - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun x : ℝ => x - 1) (𝓝 1) (𝓝 0) := by
        have h := ((continuous_sub_right (1 : ℝ)).tendsto (1 : ℝ))
        rwa [sub_self] at h
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.2 (Set.mem_Ioi.1 hx)
  exact hlim0.comp hsub

end GlobalTheory.RSThetaRes

namespace GlobalTheory.RSThetaRes

theorem residue_geometric : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∀ F : GA E a → ℂ, Continuous F → (∃ C : ℝ, ∀ g, ‖F g‖ ≤ C) → (∀ γ ∈ latticeGL E a, ∀ g, F (γ * g) = F g) → Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕 ∩ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, F g * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1 : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1) (𝓝 ((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ) * ∫ g in 𝓕', F g ∂μ)) :=
  fun _ _ _ _ _ ha μ _ _ _ h𝓕 h𝓕' _ hF ⟨_, hC⟩ hinv => tendsto_residue ha μ h𝓕 h𝓕' hF hC hinv

end GlobalTheory.RSThetaRes
