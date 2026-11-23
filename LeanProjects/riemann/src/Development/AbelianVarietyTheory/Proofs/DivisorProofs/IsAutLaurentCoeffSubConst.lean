import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalCenterEqCircleIntegralShiftedOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CircleIntegralZpowMulHoloMulEqSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCircleIntegralFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateEisensteinHolomorphicBallStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateEisensteinHolomorphicDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinResidueHolomorphicRegionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinResidueHolomorphicRegionTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinResidueHolomorphicRegionTwo
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LaurentAut

open GlobalTheory.EisCont.Smooth
open scoped ContDiff

theorem hasDerivAt_integral_cpt {𝕜 : Type} [RCLike 𝕜] [NormedSpace 𝕜 ℂ] [ProperSpace 𝕜] {H : Type} [TopologicalSpace H] [T2Space H]
    [MeasurableSpace H] [OpensMeasurableSpace H] (μ : Measure H) [IsFiniteMeasureOnCompacts μ] {Φ Φ' : 𝕜 → H → ℂ} {x₀ : 𝕜}
    {C : Set H} (hC : IsCompact C) (hc : ∀ t, Continuous (Φ t)) (hc' : Continuous fun p : 𝕜 × H => Φ' p.1 p.2)
    (h0 : ∀ t ∈ Metric.closedBall x₀ 1, ∀ y ∉ C, Φ t y = 0 ∧ Φ' t y = 0)
    (hd : ∀ t y, HasDerivAt (Φ · y) (Φ' t y) t) :
    HasDerivAt (fun t => ∫ y, Φ t y ∂μ) (∫ y, Φ' x₀ y ∂μ) x₀ := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ 1).prod hC).exists_bound_of_continuousOn hc'.continuousOn
  have hx : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one
  have hc0 : Continuous (Φ' x₀) := hc'.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := C.indicator fun _ => B)
    (Metric.closedBall_mem_nhds x₀ one_pos) ?_
    ((hc x₀).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).1))
    (hc0.integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 x₀ hx y hy).2)).aestronglyMeasurable
    (.of_forall fun y t ht => ?_) ?_ (.of_forall fun y t _ => hd t y)).2
  · filter_upwards [Metric.closedBall_mem_nhds x₀ one_pos] with t ht
    exact ((hc t).integrable_of_hasCompactSupport (.intro hC fun y hy => (h0 t ht y hy).1)).aestronglyMeasurable
  · by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy]; exact hB (t, y) ⟨ht, hy⟩
    · rw [Set.indicator_of_notMem hy, (h0 t ht y hy).2, norm_zero]
  · exact (integrable_indicator_iff hC.measurableSet).2 (integrableOn_const hC.measure_lt_top.ne)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Abstract

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] {N : ℕ}
  {j : H →* G} {ι : H →* Matrix (Fin N) (Fin N) ℂ}

def IsWt (f : Matrix (Fin N) (Fin N) ℂ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∃ S, IsCompact S ∧ (∀ B ∈ S, B.det ≠ 0) ∧ ∀ y, f y ≠ 0 → y ∈ S

theorem isWt_of_isBump {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hf : IsBump f) : IsWt f := ⟨hf.smooth, hf.supp⟩

theorem fderiv_supp {f : Matrix (Fin N) (Fin N) ℂ → ℝ} {S : Set (Matrix (Fin N) (Fin N) ℂ)} (hS : IsCompact S)
    (hfS : ∀ y, f y ≠ 0 → y ∈ S) {y : Matrix (Fin N) (Fin N) ℂ} (hy : y ∉ S) : fderiv ℝ f y = 0 := by
  by_contra h
  exact hy (closure_minimal (fun z hz => hfS z hz) hS.isClosed (support_fderiv_subset ℝ (f := f) h))

theorem IsWt.der {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hf : IsWt f) (M : Matrix (Fin N) (Fin N) ℂ) :
    IsWt fun X => fderiv ℝ f X (X * M) := by
  obtain ⟨h1, S, hS, hd, hfS⟩ := hf
  refine ⟨(h1.fderiv_right (m := ∞) le_rfl).clm_apply
    (CompanionTheory.D.gk.admitted.Gard.contDiff_mul.comp (contDiff_id.prodMk contDiff_const)), S, hS, hd, fun y hy => ?_⟩
  by_contra h
  exact hy (by simp only [fderiv_supp hS hfS h, ContinuousLinearMap.zero_apply])

variable [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1)
include hι h1

theorem exists_cpt {S T : Set (Matrix (Fin N) (Fin N) ℂ)} (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0)
    (hT : IsCompact T) : ∃ C : Set H, IsCompact C ∧ ∀ X ∈ T, ∀ y ∉ C, ι y⁻¹ * X ∉ S := by
  refine ⟨_, isCompact_preimage hι h1 (CompanionTheory.D.gk.admitted.Gard.isCompact_mul_inv hT hS hd), fun g hg x hx hB => ?_⟩
  refine hx ⟨(g, ι x⁻¹ * g), ⟨hg, hB⟩, ?_⟩
  have e : g = ι x * (ι x⁻¹ * g) := by rw [← Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mul]
  show g * (ι x⁻¹ * g)⁻¹ = ι x
  nth_rewrite 1 [e]
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hd _ hB).isUnit, Matrix.mul_one]

theorem IsWt.cpt {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hf : IsWt f) :
    (Continuous fun y => f (ι y⁻¹ * 1)) ∧ ∃ C : Set H, IsCompact C ∧ ∀ y ∉ C, f (ι y⁻¹ * 1) = 0 := by
  obtain ⟨hs, S, hS, hd, hfS⟩ := hf
  obtain ⟨C, hC, h⟩ := exists_cpt hι h1 hS hd (isCompact_singleton (x := 1))
  exact ⟨hs.continuous.comp ((hι.continuous.comp continuous_inv).mul continuous_const), C, hC,
    fun y hy => by_contra fun e => h 1 rfl y hy (hfS _ e)⟩

variable [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem IsWt.bound {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hf : IsWt f) : ∃ (C : Set H) (I : ℝ), IsCompact C ∧ 0 ≤ I ∧
    ∀ (ψ : G → ℂ) (g : G) (M : ℝ), (∀ y ∈ C, ‖ψ (g * j y)‖ ≤ M) → ∫ y, ‖f (ι y⁻¹ * 1) • ψ (g * j y)‖ ∂μ ≤ I * M := by
  obtain ⟨hw, C, hC, h0⟩ := hf.cpt hι h1
  have hI : Integrable (fun y => ‖f (ι y⁻¹ * 1)‖) μ := (hw.integrable_of_hasCompactSupport (.intro hC h0)).norm
  refine ⟨C, ∫ y, ‖f (ι y⁻¹ * 1)‖ ∂μ, hC, integral_nonneg fun _ => norm_nonneg _, fun ψ g M hM => ?_⟩
  rw [← integral_mul_const]
  refine integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _) (hI.mul_const M) (.of_forall fun y => ?_)
  by_cases hy : y ∈ C
  · simp only [norm_smul]; exact mul_le_mul_of_nonneg_left (hM y hy) (norm_nonneg _)
  · simp only [h0 y hy, zero_smul, norm_zero, zero_mul, le_rfl]

theorem deriv_avg (hj : Continuous j) {f : Matrix (Fin N) (Fin N) ℂ → ℝ} (hf : IsWt f) {ψ : G → ℂ} (hψ : Continuous ψ)
    {x : ℝ → H} (hx : ContDiff ℝ ∞ fun t => ι (x t)) (hx0 : x 0 = 1) (g : G) :
    deriv (fun t => avg j ι μ f ψ (g * j (x t))) 0 =
      avg j ι μ (fun X => fderiv ℝ f X (X * deriv (fun t => ι (x t)) 0)) ψ g := by
  obtain ⟨hs, S, hS, hd, hfS⟩ := hf
  obtain ⟨C, hC, h⟩ := exists_cpt hι h1 hS hd ((isCompact_closedBall (0 : ℝ) 1).image hx.continuous)
  have e : (fun t => avg j ι μ f ψ (g * j (x t))) = fun t => ∫ y, f (ι y⁻¹ * ι (x t)) • ψ (g * j y) ∂μ := by
    funext t
    rw [← integral_mul_left_eq_self _ (x t)]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp [← map_mul, mul_assoc]
  have hi : Continuous fun y : H => ι y⁻¹ := hι.continuous.comp continuous_inv
  have hψ' : Continuous fun y => ψ (g * j y) := by fun_prop
  have hx' : Continuous (deriv fun t => ι (x t)) := hx.continuous_deriv (by simp)
  have key := hasDerivAt_integral_cpt μ (x₀ := (0 : ℝ)) (Φ := fun t y => f (ι y⁻¹ * ι (x t)) • ψ (g * j y))
    (Φ' := fun t y => fderiv ℝ f (ι y⁻¹ * ι (x t)) (ι y⁻¹ * deriv (fun t => ι (x t)) t) • ψ (g * j y)) hC
    (fun t => (hs.continuous.comp (hi.mul continuous_const)).smul hψ')
    ((((hs.continuous_fderiv (by simp)).comp ((hi.comp continuous_snd).mul (hx.continuous.comp continuous_fst))).clm_apply
      ((hi.comp continuous_snd).mul (hx'.comp continuous_fst))).smul (hψ'.comp continuous_snd))
    (fun t ht y hy => by
      have hn := h _ ⟨t, ht, rfl⟩ y hy
      have h2 : f (ι y⁻¹ * ι (x t)) = 0 := by_contra fun e => hn (hfS _ e)
      simp only [h2, fderiv_supp hS hfS hn, ContinuousLinearMap.zero_apply, zero_smul, and_self])
    (fun t y => by
      have d1 := (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (ι y⁻¹))).hasFDerivAt.comp_hasDerivAt t
        (hx.differentiable (by simp) t).hasDerivAt
      exact ((hs.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t d1).smul_const _)
  rw [e, key.deriv]
  simp only [avg, hx0, map_one, Matrix.mul_one]

end Abstract

section Unitary

open GlobalTheory.EisRes.CentralEig

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {N : ℕ} {ι : GInf σ J →* Matrix (Fin N) (Fin N) ℂ}
  (hι : IsEmbedding ι) (h1 : ∀ y, ‖(ι y).det‖ = 1) {f : Matrix (Fin N) (Fin N) ℂ → ℝ}
include hι h1

theorem foldr_avg (hCM : IsCMExt F E σ)
    (hx : ∀ γ, IsRealLine σ J γ → ∃ x : ℝ → GInf σ J, (∀ t, γ t = ofInf σ J (x t)) ∧ ContDiff ℝ ∞ fun t => ι (x t))
    (hf : IsWt f) : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∃ f', IsWt f' ∧ ∀ ψ, Continuous ψ →
      l.foldr lineDer (avg (ofInf σ J) ι Measure.haar f ψ) = avg (ofInf σ J) ι Measure.haar f' ψ
  | [], _ => ⟨f, hf, fun _ _ => rfl⟩
  | γ :: l, hl => by
    obtain ⟨f', hf', e⟩ := foldr_avg hCM hx hf l fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
    obtain ⟨x, ex, hxs⟩ := hx γ (hl γ List.mem_cons_self)
    have hx0 : x 0 = 1 := by
      simpa using (congrArg (projInf σ J) ((ex 0).symm.trans (line_zero hCM (hl γ List.mem_cons_self))))
    refine ⟨_, hf'.der (deriv (fun t => ι (x t)) 0), fun ψ hψ => funext fun g => ?_⟩
    rw [List.foldr_cons, e ψ hψ, ← deriv_avg hι h1 Measure.haar (continuous_ofInf σ J) hf' hψ hxs hx0 g]
    simp only [lineDer, ex]

theorem avg_growth (hf : IsWt f) (m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (ψ : GAd σ J → ℂ) (A : ℝ),
    (∀ g, ‖ψ g‖ ≤ A * (height σ J g : ℝ) ^ m) →
      ∀ g, ‖avg (ofInf σ J) ι Measure.haar f ψ g‖ ≤ K * A * (height σ J g : ℝ) ^ m := by
  obtain ⟨C, I, hC, hI, hb⟩ := hf.bound (j := ofInf σ J) hι h1 Measure.haar
  obtain ⟨c, hc⟩ := height_bddAbove_of_isCompact σ J (hC.image (continuous_ofInf σ J))
  refine ⟨I * (c : ℝ) ^ m, by positivity, fun ψ A hA g => ?_⟩
  have hA0 : 0 ≤ A := by simpa using (norm_nonneg _).trans (hA 1)
  refine (norm_integral_le_integral_norm _).trans ((hb ψ g (A * ((height σ J g : ℝ) * c) ^ m) fun y hy => ?_).trans
    (le_of_eq (by ring)))
  refine (hA _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) ?_ m) hA0)
  exact_mod_cast (height_mul_le σ J g _).trans (mul_le_mul_right (hc _ ⟨y, hy, rfl⟩) _)

theorem avg_holo (hf : IsBump f) {H₀ : ℂ → GAd σ J → ℂ} {U : Set ℂ} (hsm : ∀ s ∈ U, IsSmoothModerate σ J (H₀ s))
    (hhol : ∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U) (g : GAd σ J) :
    DifferentiableOn ℂ (fun s => avg (ofInf σ J) ι Measure.haar f (H₀ s) g) U := by
  let W : Submodule ℂ (GAd σ J → ℂ) :=
    { carrier := {ψ | Continuous ψ}
      zero_mem' := continuous_zero
      add_mem' := fun h h' => h.add h'
      smul_mem' := fun a ψ h => h.const_smul a }
  let T : W →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => avg (ofInf σ J) ι Measure.haar f ψ g
      map_add' := fun a b => by
        simpa only [avg, Submodule.coe_add, Pi.add_apply, smul_add] using
          integral_add (integrable_avg hι h1 Measure.haar (continuous_ofInf σ J) hf a.2 g)
            (integrable_avg hι h1 Measure.haar (continuous_ofInf σ J) hf b.2 g)
      map_smul' := fun c a => by
        simp only [avg, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, ← integral_smul, smul_comm c] }
  obtain ⟨μ, hμ⟩ := T.exists_extend
  have e : ∀ ψ, Continuous ψ → μ ψ = avg (ofInf σ J) ι Measure.haar f ψ g := fun ψ hψ =>
    LinearMap.congr_fun hμ ⟨ψ, hψ⟩
  refine (hhol μ fun m => ?_).congr fun s hs => (e _ (hsm s hs).cont).symm
  obtain ⟨K, -, hK⟩ := avg_growth hι h1 (isWt_of_isBump hf) m
  refine ⟨[[]], K * 1 * (height σ J g : ℝ) ^ m, by simp, fun ψ hψ _ hb => ?_⟩
  rw [e ψ hψ.cont]
  exact hK ψ 1 (fun g => by simpa using hb [] (by simp) g) g

variable {x : Matrix (Fin n) (Fin 1) E} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
  {h : GAd σ J → ℝ}

theorem avg_pow (hf : IsBump f)
    (hu : ∀ κ, (∀ w, projInfArch σ J w κ ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a)) →
      ι κ ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hI : IsIwaHtG σ J x L a h) (hc : Continuous h) : ∃ b : ℂ → ℂ, Differentiable ℂ b ∧ (∀ t : ℝ, b t ≠ 0) ∧
      ∀ t g, avg (ofInf σ J) ι Measure.haar f (fun g => (h g : ℂ) ^ t) g = b t * (h g : ℂ) ^ t := by
  obtain ⟨hw, C, hC, h0⟩ := (isWt_of_isBump hf).cpt hι h1
  have hj : Continuous fun y => h (1 * ofInf σ J y) := hc.comp (continuous_const.mul (continuous_ofInf σ J))
  have hne : ∀ g, (h g : ℂ) ≠ 0 := fun g => by exact_mod_cast (ht_pos hI g).ne'
  have hsl : ∀ g, (h g : ℂ) ∈ Complex.slitPlane := fun g => Or.inl (by simpa using ht_pos hI g)
  refine ⟨fun t => avg (ofInf σ J) ι Measure.haar f (fun g => (h g : ℂ) ^ t) 1, fun t => ?_, fun t => ?_, fun t g => ?_⟩
  · have hj' := Complex.continuous_ofReal.comp hj
    exact (hasDerivAt_integral_cpt Measure.haar (x₀ := t) (Φ := fun t y => f (ι y⁻¹ * 1) • (h (1 * ofInf σ J y) : ℂ) ^ t)
      (Φ' := fun t y => f (ι y⁻¹ * 1) • ((h (1 * ofInf σ J y) : ℂ) ^ t * Complex.log (h (1 * ofInf σ J y)))) hC
      (fun t => hw.smul (hj'.cpow continuous_const fun y => hsl _))
      ((hw.comp continuous_snd).smul (((hj'.comp continuous_snd).cpow continuous_fst fun y => hsl _).mul
        ((hj'.comp continuous_snd).clog fun y => hsl _)))
      (fun t _ y hy => by simp only [h0 y hy, zero_smul, and_self])
      (fun t y => ((Complex.hasStrictDerivAt_const_cpow (Or.inl (hne _))).hasDerivAt).const_smul
        (f (ι y⁻¹ * 1)))).differentiableAt
  · have e : avg (ofInf σ J) ι Measure.haar f (fun g => (h g : ℂ) ^ (t : ℂ)) 1 =
        ((∫ y, f (ι y⁻¹ * 1) * h (1 * ofInf σ J y) ^ t ∂Measure.haar : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (.of_forall fun y => ?_)
      simp only [Complex.ofReal_mul, Complex.real_smul, Complex.ofReal_cpow (ht_pos hI _).le]
    have hpos := (hw.mul (hj.rpow_const fun y => Or.inl (ht_pos hI _).ne')).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (μ := Measure.haar) (x := 1) (HasCompactSupport.mul_right (.intro hC h0) (f' := fun y => h (1 * ofInf σ J y) ^ t))
      (fun y => mul_nonneg (hf.nonneg _) (Real.rpow_pos_of_pos (ht_pos hI _) t).le)
      (mul_ne_zero (by simpa using hf.one) (Real.rpow_pos_of_pos (ht_pos hI _) t).ne')
    show avg (ofInf σ J) ι Measure.haar f (fun g => (h g : ℂ) ^ (t : ℂ)) 1 ≠ 0
    rw [e]
    exact_mod_cast hpos.ne'
  · obtain ⟨p, k, hk, rfl⟩ := exists_iwa hI g
    rw [avg_mul hι h1 Measure.haar hf (κ := projInf σ J k) (hu _ fun w => by simpa using (mem_levelAll.1 hk).2 w)
      (fun y => ext_inf_fin σ J (by simp) (by simp))]
    simp only [avg, ht_right hI _ hk, pow_left hI p.2, one_mul, ← integral_mul_const, smul_mul_assoc, mul_comm ((h p : ℂ) ^ t)]

end Unitary

open GlobalTheory.EisRes.CentralEig in

theorem uniform_growth_near_rho {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E}
    {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)} {h : GAd σ J → ℝ} {Eis : ℂ → GAd σ J → ℂ}
    (hS : HidaSetting σ J X Y L a h) (hP : IsSerG σ J (col0 X) h Eis) {k₀ : ℕ} {U₀ : Set ℂ} {H₀ : ℂ → GAd σ J → ℂ}
    (hU₀ : U₀ ∈ 𝓝 (((n : ℂ) - 1) / 2))
    (hH : ∀ s ∈ U₀, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H₀ s g = (s - (((n : ℂ) - 1) / 2)) ^ k₀ * Eis s g)
    (hsm : ∀ s ∈ U₀, IsSmoothModerate σ J (H₀ s))
    (hhol : ∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) U₀) :
    ∃ V ∈ 𝓝 (((n : ℂ) - 1) / 2), ∃ m : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ C : ℝ, ∀ s ∈ V, ∀ g, ‖l.foldr lineDer (H₀ s) g‖ ≤ C * (height σ J g : ℝ) ^ m := by
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  have hρre : ρ.re = ((n : ℝ) - 1) / 2 := by simp [hρ]
  have hc : Continuous h := HtCont.continuous_iwaHt F E σ n J r X Y L a h hS
  have hcmp := iwaHt_mul_le_of_isCompact F E σ n J r X Y L a h hS
  obtain ⟨hCM, -, hJ, hn, -, hA, hI⟩ := hS
  obtain ⟨N, ι, hι, h1, hu, hx⟩ := exists_mat hCM hJ fun w => Formalism.UG.bc (compInf F E w) a
  obtain ⟨f, hf, -, -⟩ := exists_bump hι h1 Measure.haar (V := Set.univ) univ_mem
  obtain ⟨b, hbd, hb0, hb⟩ := avg_pow hι h1 hf hu hI hc
  obtain ⟨T, hT⟩ := exists_reps σ J (col0 X)
  have heig : ∀ s : ℂ, ρ.re < s.re → ∀ g, avg (ofInf σ J) ι Measure.haar f (Eis s) g = b (s + ρ) * Eis s g := by
    intro s hs g
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hre : 0 ≤ (s + ρ).re := by rw [Complex.add_re]; rw [hρre] at hs ⊢; linarith
    rw [hρre] at hs
    have hsum := hP T hT s hs
    haveI : Countable T := by
      have := (hsum g).summable.countable_support
      rw [Function.support_eq_univ fun t => by
        simp only [ne_eq, Complex.cpow_eq_zero_iff, Complex.ofReal_eq_zero, (ht_pos hI _).ne', false_and,
          not_false_eq_true]] at this
      exact Set.countable_univ_iff.1 this
    obtain ⟨C, I, hC, hI0, hbd⟩ := (isWt_of_isBump hf).bound (j := ofInf σ J) hι h1 Measure.haar
    obtain ⟨K, hK0, hK⟩ := hcmp _ (hC.image (continuous_ofInf σ J))
    have hcp : Continuous fun g => (h g : ℂ) ^ (s + ρ) :=
      (Complex.continuous_ofReal.comp hc).cpow continuous_const fun g => Or.inl (by simpa using ht_pos hI g)
    have key := hasSum_integral_of_summable_integral_norm (μ := Measure.haar)
      (F := fun (t : T) y => f (ι y⁻¹ * 1) • (h (t.1.1 * g * ofInf σ J y) : ℂ) ^ (s + ρ))
      (fun t => integrable_avg hι h1 Measure.haar (continuous_ofInf σ J) hf hcp _)
      (.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _)
        (fun t => hbd (fun g => (h g : ℂ) ^ (s + ρ)) (t.1.1 * g) (K ^ (s + ρ).re * ‖(h (t.1.1 * g) : ℂ) ^ (s + ρ)‖)
          fun y hy => by
            rw [Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hI _), Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hI _),
              ← Real.mul_rpow hK0 (ht_pos hI _).le]
            exact Real.rpow_le_rpow (ht_pos hI _).le (hK _ _ ⟨y, hy, rfl⟩) hre)
        (((summable_norm_iff.2 (hsum g).summable).mul_left _).mul_left _))
    have e1 : (fun t : T => ∫ y, f (ι y⁻¹ * 1) • (h (t.1.1 * g * ofInf σ J y) : ℂ) ^ (s + ρ) ∂Measure.haar) =
        fun t : T => b (s + ρ) * (h (t.1.1 * g) : ℂ) ^ (s + ρ) := funext fun t => hb (s + ρ) (t.1.1 * g)
    have e2 : (fun y => ∑' t : T, f (ι y⁻¹ * 1) • (h (t.1.1 * g * ofInf σ J y) : ℂ) ^ (s + ρ)) =
        fun y => f (ι y⁻¹ * 1) • Eis s (g * ofInf σ J y) := funext fun y => by
      simpa only [mul_assoc] using ((hsum (g * ofInf σ J y)).const_smul (f (ι y⁻¹ * 1))).tsum_eq
    rw [e1, e2] at key
    exact key.unique ((hsum g).mul_left _)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU₀
  have hbd' : Differentiable ℂ fun s => b (s + ρ) := hbd.comp (differentiable_id.add_const ρ)
  have hall : ∀ g, ∀ s ∈ Metric.ball ρ ε, avg (ofInf σ J) ι Measure.haar f (H₀ s) g = b (s + ρ) * H₀ s g := by
    intro g
    have a1 := ((avg_holo hι h1 hf hsm hhol g).mono hball).analyticOnNhd Metric.isOpen_ball
    have hd : DifferentiableOn ℂ (fun s => H₀ s g) (Metric.ball ρ ε) :=
      (hhol _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)).mono hball
    have a2 := (hbd'.differentiableOn.fun_mul hd).analyticOnNhd Metric.isOpen_ball
    set z₀ : ℂ := ρ + ((ε / 2 : ℝ) : ℂ) with hz₀
    have hz₀b : z₀ ∈ Metric.ball ρ ε := by
      rw [Metric.mem_ball, hz₀, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    have hz₀re : ρ.re < z₀.re := by simp [hz₀, hε]
    have hopen : IsOpen (Metric.ball ρ ε ∩ {s : ℂ | ρ.re < s.re}) :=
      Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
    refine a1.eqOn_of_preconnected_of_eventuallyEq a2 (convex_ball ρ ε).isPreconnected hz₀b ?_
    filter_upwards [hopen.mem_nhds ⟨hz₀b, hz₀re⟩] with s hs'
    have hne : s ≠ ρ := by rintro rfl; exact lt_irrefl ρ.re hs'.2
    rw [hH s (hball hs'.1) hne, mul_left_comm, ← heig s hs'.2 g]
    simp only [avg, hH s (hball hs'.1) hne, ← integral_const_mul, mul_smul_comm]
  have hρ0 : b (ρ + ρ) ≠ 0 := by
    have : ρ + ρ = (((n : ℝ) - 1 : ℝ) : ℂ) := by rw [hρ]; push_cast; ring
    rw [this]; exact hb0 _
  have hV : ∀ᶠ s in 𝓝 ρ, b (s + ρ) ≠ 0 ∧ ‖(b (s + ρ))⁻¹‖ < ‖(b (ρ + ρ))⁻¹‖ + 1 :=
    (hbd'.continuous.continuousAt.eventually_ne hρ0).and
      ((hbd'.continuous.continuousAt.inv₀ hρ0).norm.eventually (gt_mem_nhds (lt_add_one _)))
  obtain ⟨-, m, A, hmA⟩ := GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ (Metric.ball ρ ε)
    (Metric.closedBall ρ (ε / 2)) Metric.isOpen_ball (isCompact_closedBall _ _)
    (Metric.closedBall_subset_ball (half_lt_self hε)) (fun s hs => hsm s (hball hs))
    (fun μ hμ => (hhol μ hμ).mono hball) [] (by simp)
  refine ⟨_, inter_mem hV (Metric.closedBall_mem_nhds ρ (half_pos hε)), m, fun l hl => ?_⟩
  obtain ⟨f', hf', e⟩ := foldr_avg hι h1 hCM hx (isWt_of_isBump hf) l hl
  obtain ⟨K, hK0, hK⟩ := avg_growth hι h1 hf' m
  refine ⟨(‖(b (ρ + ρ))⁻¹‖ + 1) * (K * A), fun s hs g => ?_⟩
  have hsb : s ∈ Metric.ball ρ ε := Metric.closedBall_subset_ball (half_lt_self hε) hs.2
  have e1 : avg (ofInf σ J) ι Measure.haar f (H₀ s) = b (s + ρ) • H₀ s := funext fun g => hall g s hsb
  have e2 : l.foldr lineDer (b (s + ρ) • H₀ s) g = b (s + ρ) * l.foldr lineDer (H₀ s) g := by
    have := congrFun (GlobalTheory.UAut.dop_smul (Finsupp.single l 1) (b (s + ρ)) (H₀ s)) g
    simpa [GlobalTheory.UAut.dop] using this
  have e3 : l.foldr lineDer (H₀ s) g = (b (s + ρ))⁻¹ * avg (ofInf σ J) ι Measure.haar f' (H₀ s) g := by
    rw [← e _ (hsm s (hball hsb)).cont, e1, e2, inv_mul_cancel_left₀ hs.1.1]
  rw [e3, norm_mul, mul_assoc]
  exact mul_le_mul hs.1.2.le (hK _ A (hmA s hs.2) g) (norm_nonneg _) (by positivity)

set_option maxHeartbeats 1000000 in

theorem isAut_laurentCoeff_sub_const : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∀ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 (((n : ℂ) - 1) / 2) → (∀ g, DifferentiableOn ℂ (H · g) U) →
      (∀ s ∈ U, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, H s g = (s - (((n : ℂ) - 1) / 2)) ^ k * Eis s g) →
      ∀ c₀ : ℂ, GlobalTheory.UAut.IsAut σ J (levelAll σ J L a ⊓ infPts σ J) (fun g => H (((n : ℂ) - 1) / 2) g - c₀) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP k U H hU hHd hHe c₀
  obtain ⟨k₀, U₀, H₀, hU₀, hH₀e, hH₀sm, hH₀hol⟩ := hP.2.2.2.1 (((n : ℂ) - 1) / 2)
  obtain ⟨V₁, hV₁, hE1⟩ := GlobalTheory.T.eisenstein_residue_holomorphic_region F E σ n J r X Y L a h Eis c hS hP k₀ U₀ H₀ hU₀ hH₀e hH₀sm hH₀hol
  obtain ⟨V₂, hV₂, hE2⟩ := GlobalTheory.T.exists_nhds_dop_central_eq_holomorphic_smul F E σ n J r X Y L a h Eis c hS hP k₀ U₀ H₀ hU₀ hH₀e hH₀sm hH₀hol
  obtain ⟨V₃, hV₃, m, hE3⟩ := uniform_growth_near_rho hS hP.1 hU₀ hH₀e hH₀sm hH₀hol
  obtain ⟨hCM, -, hJ, -, -, hA, -⟩ := hS
  haveI := hA.lat
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  set W : Set ℂ := interior (U ∩ U₀ ∩ (V₁ ∩ V₃) ∩ V₂) with hWdef
  have hWo : IsOpen W := isOpen_interior
  have hWn : W ∈ 𝓝 ρ := interior_mem_nhds.2 (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hU hU₀) (Filter.inter_mem hV₁ hV₃)) hV₂)
  have hWU : W ⊆ U := fun x hx => (interior_subset hx).1.1.1
  have hWU₀ : W ⊆ U₀ := fun x hx => (interior_subset hx).1.1.2
  have hWV₁ : W ⊆ V₁ := fun x hx => (interior_subset hx).1.2.1
  have hWV₃ : W ⊆ V₃ := fun x hx => (interior_subset hx).1.2.2
  have hWV₂ : W ⊆ interior V₂ := interior_mono fun x hx => hx.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hWn
  have hr : (0 : ℝ) < ε / 2 := by linarith
  have hcb : Metric.closedBall ρ (ε / 2) ⊆ W := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hsph : Metric.sphere ρ (ε / 2) ⊆ W := Metric.sphere_subset_closedBall.trans hcb
  have hsmW : ∀ s ∈ W, IsSmoothModerate σ J (H₀ s) := fun s hs => hH₀sm s (hWU₀ hs)
  have hholW : ∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) W :=
    fun μ hμ => (hH₀hol μ hμ).mono hWU₀
  have hH₀d : ∀ g, DifferentiableOn ℂ (H₀ · g) W := fun g => hholW _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)
  let Rj : ℤ → GAd σ J → ℂ := fun j g => circleIntegral (fun z => (z - ρ) ^ j * H₀ z g) ρ (ε / 2)
  have hHR : ∀ g, H ρ g = (2 * ↑Real.pi * Complex.I)⁻¹ * Rj ((k : ℤ) - k₀ - 1) g :=
    GlobalTheory.eval_center_eq_circleIntegral_shifted_order ρ k k₀ (ε / 2) W Eis H H₀ hr hWo hcb (fun g => (hHd g).mono hWU) hH₀d
      (fun s hs hne g => hHe s (hWU hs) hne g) (fun s hs hne g => hH₀e s (hWU₀ hs) hne g)
  have hinv : ∀ j g, ∀ k ∈ levelAll σ J L a, Rj j (g * k) = Rj j g := fun j g k hk =>
    circleIntegral.integral_congr hr.le fun z hz => by
      simp only [hE1 z (hWV₁ (hsph hz)) k hk g]
  have hzfin : ∀ j, FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, GlobalTheory.UAut.IsCentral σ J z ∧ f = GlobalTheory.UAut.dop z (Rj j)}) := by
    intro j
    haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range fun i : Fin (-j).toNat => Rj (j + i))
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun i : Fin (-j).toNat => Rj (j + i)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨χ, hχ, hχe⟩ := hE2 z hz
    obtain ⟨cc, hcc⟩ := GlobalTheory.circleIntegral_zpow_mul_holo_mul_eq_sum ρ (ε / 2) W χ H₀ hr hWo hcb (hχ.mono hWV₂) hH₀d j
    have e : GlobalTheory.UAut.dop z (Rj j) = ∑ i : Fin (-j).toNat, cc i • Rj (j + i) := by
      funext g
      rw [GlobalTheory.T.moderate_eisenstein_holomorphic_derivative F E σ hCM n J hJ H₀ ρ (ε / 2) W hWo hr hcb hsmW hholW j z hz.1 g]
      rw [circleIntegral.integral_congr hr.le (g := fun w => (w - ρ) ^ j * (χ w * H₀ w g)) fun w hw => by
        simp only [hχe w (interior_subset (hWV₂ (hsph hw))), Pi.smul_apply, smul_eq_mul]]
      rw [hcc g, Finset.sum_apply]
      exact (Fin.sum_univ_eq_sum_range (fun i => cc i * circleIntegral (fun w => (w - ρ) ^ (j + (i : ℤ)) * H₀ w g) ρ (ε / 2)) _).symm
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have haut : ∀ j, GlobalTheory.UAut.IsAut σ J (levelAll σ J L a ⊓ infPts σ J) (Rj j) := by
    intro j
    have hleft : ∀ γ ∈ ratPts σ J, ∀ g, Rj j (γ * g) = Rj j g := fun γ hγ g =>
      circleIntegral.integral_congr hr.le fun z hz => by
        simp only [(hsmW z (hsph hz)).left γ hγ g]
    have hlev : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, Rj j (g * k) = Rj j g :=
      ⟨levelOpen σ J L, isOpen_levelOpen σ J L, fun k hk hkf g => hinv j g k (mem_levelAll.2
        ⟨mem_levelOpen.1 hk, fun w => by rw [mem_finPts_iff_forall.1 hkf w]; exact one_mem _⟩)⟩
    have hcont := GlobalTheory.CircleCont.continuous_circleIntegral_family F E σ hCM n J hJ H₀ ρ (ε / 2) W hWo hr hcb hsmW hholW j
    have hsm := GlobalTheory.T.moderate_eisenstein_holomorphic_ball F E σ hCM n J hJ H₀ ρ (ε / 2) W hWo hr hcb hsmW hholW j
    have hkf : GlobalTheory.Doubling.IsKFinite (levelAll σ J L a ⊓ infPts σ J) (Rj j) :=
      GlobalTheory.Doubling.IsKFinite.of_invariant fun g k hk => hinv j g k (Subgroup.mem_inf.1 hk).1
    have hgr : ∃ N : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
        ∃ C : ℝ, ∀ g, ‖l.foldr lineDer (Rj j) g‖ ≤ C * (height σ J g : ℝ) ^ N := by
      refine ⟨m, fun l hl => ?_⟩
      obtain ⟨C, hC⟩ := hE3 l hl
      refine ⟨2 * Real.pi * (ε / 2) * ((ε / 2) ^ j * C), fun g => ?_⟩
      have e := GlobalTheory.T.moderate_eisenstein_holomorphic_derivative F E σ hCM n J hJ H₀ ρ (ε / 2) W hWo hr hcb hsmW hholW j (Finsupp.single l 1)
        (fun l' hl' => by rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hl')]; exact hl) g
      simp only [GlobalTheory.UAut.dop, zero_mul, Finsupp.sum_single_index, one_mul] at e
      have hb : ∀ z ∈ Metric.sphere ρ (ε / 2),
          ‖(z - ρ) ^ j * l.foldr lineDer (H₀ z) g‖ ≤ (ε / 2) ^ j * C * (height σ J g : ℝ) ^ m := by
        intro z hz
        have hz' : ‖z - ρ‖ = ε / 2 := by simpa [dist_eq_norm] using hz
        rw [norm_mul, norm_zpow, hz', mul_assoc]
        exact mul_le_mul_of_nonneg_left (hC z (hWV₃ (hsph hz)) g) (zpow_nonneg hr.le j)
      refine (congrArg norm e).le.trans ((circleIntegral.norm_integral_le_of_norm_le_const hr.le hb).trans (le_of_eq ?_))
      ring
    exact ⟨⟨hleft, hlev, hcont, hsm, hgr⟩, GlobalTheory.UAut.kfin_iff.2 hkf, hzfin j⟩
  have e : (fun g => H ρ g - c₀) = (fun _ => -c₀) + (2 * ↑Real.pi * Complex.I)⁻¹ • Rj ((k : ℤ) - k₀ - 1) := by
    funext g; simp only [hHR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]
  have h1 := GlobalTheory.UAut.isAut_iff_isAutOn.1 (haut ((k : ℤ) - k₀ - 1))
  have h2 := (GlobalTheory.UAut.isAutOn_add_smul F E σ hCM n J hJ _ _ _ _ ((2 * ↑Real.pi * Complex.I)⁻¹) h1 h1).2
  exact GlobalTheory.UAut.isAut_iff_isAutOn.2
    (GlobalTheory.UAut.isAutOn_add_smul F E σ hCM n J hJ _ _ _ _ 1 (GlobalTheory.UAut.isAutOn_const σ J _ _ (-c₀)) h2).1

end GlobalTheory.LaurentAut
end
