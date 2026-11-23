import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactCoverIffRapidDecOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

open scoped ENNReal Topology Matrix

namespace GlobalTheory.KAvgApprox

open Formalism.REAL GlobalTheory.TypeSum

theorem approx_family : ∀ (n : ℕ) (ε : Fin n → Bool) (ι : Type) (F : ι → KG ε → ℂ), (∀ i, Continuous (F i)) →
    (∃ M : ℝ, ∀ i k, ‖F i k‖ ≤ M) → (∀ δ : ℝ, 0 < δ → ∀ᶠ k in 𝓝 (1 : KG ε), ∀ i, ‖F i k - F i 1‖ < δ) →
    ∀ δ : ℝ, 0 < δ → ∃ e : KG ε → ℂ, KFinFun ε e ∧ ∀ i, ‖F i 1 - ∫ k, e k * F i k ∂(muK ε)‖ ≤ δ := by
  intro n ε ι F hFc ⟨M, hM⟩ hequi δ hδ
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  obtain ⟨U, hU, hUo, h1U⟩ := eventually_nhds_iff.1 (hequi (δ / 3) (by positivity))
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed (X := KG ε)
    hUo.isClosed_compl isClosed_singleton (Set.disjoint_singleton_right.2 (fun h => h h1U))
  have hfn : 0 ≤ (f : KG ε → ℝ) := fun k => (hf01 k).1
  have hf1' : f 1 = 1 := hf1 rfl
  have hc : 0 < ∫ k, f k ∂(muK ε) :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (HasCompactSupport.of_compactSpace _) hfn (by rw [hf1']; norm_num)
  set c := ∫ k, f k ∂(muK ε) with hcdef
  let g : C(KG ε, ℂ) := ⟨fun k => ((f k / c : ℝ) : ℂ), by fun_prop⟩
  have hgk : ∀ k, g k = ((f k / c : ℝ) : ℂ) := fun k => rfl
  have hgint : ∫ k, g k ∂(muK ε) = 1 := by
    simp only [hgk]
    rw [integral_complex_ofReal, integral_div, ← hcdef, div_self hc.ne']
    simp
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hMb : ∀ i k, ‖F i k‖ ≤ M' := fun i k => (hM i k).trans (le_max_left _ _)
  have hgcl : g ∈ closure ((GlobalTheory.KFinSep.finAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, GlobalTheory.KFinSep.finAlg_dense]; trivial
  set η := δ / (3 * (M' + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨p, hp, hpg⟩ := Metric.mem_closure_iff.1 hgcl η hη0
  have hpk : ∀ k, ‖g k - p k‖ ≤ η := fun k => by
    have := ContinuousMap.norm_coe_le_norm (g - p) k
    rw [dist_eq_norm] at hpg
    simp only [ContinuousMap.sub_apply] at this
    linarith
  refine ⟨p, hp.1, fun x => le_of_lt ?_⟩
  have hFx : Continuous (F x) := hFc x
  have hi1 : Integrable (fun k => g k * F x 1) (muK ε) :=
    (g.continuous.mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun k => p k * F x k) (muK ε) :=
    (p.continuous.mul hFx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hid : F x 1 - ∫ k, p k * F x k ∂(muK ε) =
      ∫ k, (g k * (F x 1 - F x k) + (g k - p k) * F x k) ∂(muK ε) := by
    have : (fun k => g k * (F x 1 - F x k) + (g k - p k) * F x k) = fun k => g k * F x 1 - p k * F x k := by
      funext k; ring
    rw [this, integral_sub hi1 hi2, integral_mul_const, hgint, one_mul]
  rw [hid]
  have hbd : ∀ k, ‖g k * (F x 1 - F x k) + (g k - p k) * F x k‖ ≤ f k / c * (δ / 3) + η * M' := by
    intro k
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, hgk, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hfn k) hc.le)]
      by_cases hk : k ∈ U
      · exact mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact (hU k hk x).le)
          (div_nonneg (hfn k) hc.le)
      · have : f k = 0 := hf0 hk
        simp [this]
    · rw [norm_mul]
      exact mul_le_mul (hpk k) (hMb x k) (norm_nonneg _) hη0.le
  have hbi : Integrable (fun k => f k / c * (δ / 3) + η * M') (muK ε) :=
    (by fun_prop : Continuous fun k => f k / c * (δ / 3) + η * M').integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine (norm_integral_le_of_norm_le hbi (Filter.Eventually.of_forall hbd)).trans_lt ?_
  rw [integral_add ((by fun_prop : Continuous fun k => f k / c * (δ / 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (integrable_const _), integral_mul_const, integral_div, ← hcdef,
    div_self hc.ne', integral_const]
  simp only [probReal_univ, one_smul, one_mul]
  have : η * M' < δ / 3 := by
    rw [hη, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

end GlobalTheory.KAvgApprox

namespace GlobalTheory.KAvgApprox

theorem unif_right : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), RapidDec V φ → ∀ (K : Type) [TopologicalSpace K]
    [CompactSpace K] (a : K → GA D V), Continuous a → ∀ (k₀ : K) (δ : ℝ), 0 < δ →
    ∀ᶠ k in 𝓝 k₀, ∀ x, ‖φ (x * a k) - φ (x * a k₀)‖ < δ := by
  intro D V φ hφ K _ _ a ha k₀ δ hδ
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨C, hC⟩ := hφ.decay 1
  obtain ⟨H, hH⟩ := isCompact_univ.exists_bound_of_continuousOn ((continuous_height V).comp ha).continuousOn
  have hHk : ∀ k, height V (a k) ≤ H := fun k => (le_abs_self _).trans (by
    simpa [Real.norm_eq_abs] using hH k (Set.mem_univ k))
  have hH1 : 1 ≤ H := (one_le_height V _).trans (hHk k₀)
  set T : ℝ := 2 * |C| / δ + 1 with hTdef
  have hT1 : 1 ≤ T := by rw [hTdef]; have : 0 ≤ 2 * |C| / δ := by positivity
                         linarith
  have hT : ∀ y, T ≤ quotHeight V y → ‖φ y‖ < δ / 2 := by
    intro y hy
    by_contra hcon
    push_neg at hcon
    have h1 := hC y
    simp only [pow_one] at h1
    have h2 : δ / 2 * T = |C| + δ / 2 := by rw [hTdef]; field_simp
    have h3 : δ / 2 * T ≤ ‖φ y‖ * quotHeight V y :=
      mul_le_mul hcon hy (by linarith) (norm_nonneg _)
    have h4 := le_abs_self C
    linarith
  have hfar : ∀ x k, T * H ≤ quotHeight V x → T ≤ quotHeight V (x * a k) := by
    intro x k hx
    have h1 := ((GlobalTheory.Size.quotHeight_laws V).2.2.1 x (a k)).2
    have hp := height_pos V (a k)
    refine le_trans ?_ h1
    rw [le_div_iff₀ hp]
    exact le_trans (mul_le_mul_of_nonneg_left (hHk k) (by linarith)) hx
  have hΩ := GlobalTheory.Grow.isCompact_setOf_height_le V (T * H + 1)
  have hev : ∀ᶠ k in 𝓝 k₀, ∀ y ∈ {g : GA D V | height V g ≤ T * H + 1}, ‖φ (y * a k) - φ (y * a k₀)‖ < δ := by
    refine hΩ.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : K × GA D V => φ (z.2 * a z.1) - φ (z.2 * a k₀) :=
      (hφ.continuous.comp (continuous_snd.mul (ha.comp continuous_fst))).sub
        (hφ.continuous.comp (continuous_snd.mul continuous_const))
    have ht := (hc.tendsto (k₀, y)).norm
    simp only [sub_self, norm_zero] at ht
    exact ht.eventually (gt_mem_nhds hδ)
  refine hev.mono fun k hk x => ?_
  by_cases hx : T * H ≤ quotHeight V x
  · have h1 := hT _ (hfar x k hx)
    have h2 := hT _ (hfar x k₀ hx)
    calc ‖φ (x * a k) - φ (x * a k₀)‖ ≤ ‖φ (x * a k)‖ + ‖φ (x * a k₀)‖ := norm_sub_le _ _
      _ < δ := by linarith
  · push_neg at hx
    obtain ⟨γ, hγ⟩ : ∃ γ : GQ V, height V (γ * x) < T * H + 1 :=
      exists_lt_of_ciInf_lt (f := fun γ : GQ V => height V (γ * x)) (by
        change quotHeight V x < T * H + 1
        linarith)
    have := hk ((γ : GA D V) * x) hγ.le
    simpa only [mul_assoc, hφ.left γ.2] using this

end GlobalTheory.KAvgApprox

namespace GlobalTheory.KAvgApprox

open GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate GlobalTheory.RealAverage

variable {D : D7} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau}
  {K : Type} [TopologicalSpace K] {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ}

section Fam

variable {𝒟 : Set (GA D V → ℂ)} (hθ : IsInfFam θ) (hκ : Continuous κ)
  (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (h𝒟 : ∀ ψ ∈ 𝒟, Continuous ψ ∧ ψ ∈ SmFun θ V)
include hθ hκ hU h𝒟

theorem famSpan_cont' : ∀ F ∈ famSpan θ V τ κ 𝒟, Continuous fun p : K × GA D V => F p.1 p.2 := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  intro F hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hx
    exact (hc.comp continuous_fst).mul
      ((h𝒟 ψ hψ).1.comp (continuous_snd.mul ((continuous_atTau hθ hκ hU).comp continuous_fst)))
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.mul hx

omit hκ in

theorem famSpan_sm' : ∀ F ∈ famSpan θ V τ κ 𝒟, ∀ k, F k ∈ SmFun θ V := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hx
    intro k
    exact (SmFun θ V).smul_mem (c k) (rTr_mem hθ (isRealPt_atTau hθ τ (hU k)) (h𝒟 ψ hψ).2)
  | zero => exact fun _ => zero_mem _
  | add x y _ _ hx hy => exact fun k => add_mem (hx k) (hy k)
  | smul a x _ hx => exact fun k => (SmFun θ V).smul_mem a (hx k)

end Fam

section Der

variable {𝒟 : Set (GA D V → ℂ)} (hθ : IsInfFam θ) (hκ : Continuous κ)
  (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (h𝒟 : ∀ ψ ∈ 𝒟, Continuous ψ ∧ ψ ∈ SmFun θ V)
  (hR : ∀ ψ ∈ 𝒟, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ 𝒟)
include hθ hκ hU h𝒟 hR

theorem famSpan_Rder_gen' {c : K → ℂ} (hc : Continuous c) {ψ : GA D V → ℂ} (hψ : ψ ∈ 𝒟) (τ' : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ') :
    (fun k => Rder θ V τ' X (fun x => c k * ψ (x * atTau θ V τ (κ k)))) ∈ famSpan θ V τ κ 𝒟 := by
  set Z : Fin V.rank × Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun a => Matrix.single a.1 a.2 1
  set X1 := fun a => (1 / 2 : ℂ) • (Z a + conjAt V τ' (Z a))
  set X2 := fun a => (1 / (2 * Complex.I) : ℂ) • (Z a - conjAt V τ' (Z a))
  set Y := fun k => adAt θ (atTau θ V τ (κ k)) τ' X
  have e : (fun k => Rder θ V τ' X (fun x => c k * ψ (x * atTau θ V τ (κ k)))) =
      ∑ a : Fin V.rank × Fin V.rank, ((fun k x => (c k * Y k a.1 a.2) * Rder θ V τ' (X1 a) ψ (x * atTau θ V τ (κ k))) +
        (fun k x => (c k * Y k a.1 a.2 * Complex.I) * Rder θ V τ' (X2 a) ψ (x * atTau θ V τ (κ k)))) := by
    funext k
    have hh := isRealPt_atTau hθ τ (hU k)
    have hsm : ψ ∈ SmFun θ V := (h𝒟 ψ hψ).2
    rw [show (fun x => c k * ψ (x * atTau θ V τ (κ k))) = c k • rTr V (atTau θ V τ (κ k)) ψ from rfl, Rder_smul,
      Rder_rTr hθ hh hX, GlobalTheory.Size.Rder_eq_sum_glDer hθ hsm (adAt_mem hh hX)]
    funext x
    simp only [Pi.smul_apply, rTr, Finset.sum_apply, smul_eq_mul, GlobalTheory.Size.glDer, RderC, Pi.add_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Y, X1, X2, Z]
    ring
  rw [e]
  have cY : ∀ a : Fin V.rank × Fin V.rank, Continuous fun k => c k * Y k a.1 a.2 := fun a =>
    hc.mul ((continuous_adAt_atTau hθ hκ hU τ' X).matrix_elem a.1 a.2)
  refine Submodule.sum_mem _ fun a _ => add_mem (Submodule.subset_span ⟨_, cY a, _, hR ψ hψ τ' _ ?_, rfl⟩)
    (Submodule.subset_span ⟨_, (cY a).mul continuous_const, _, hR ψ hψ τ' _ ?_, rfl⟩)
  · exact (GlobalTheory.SmoothAutCheck.parts_mem V τ' (Z a)).1
  · exact (GlobalTheory.SmoothAutCheck.parts_mem V τ' (Z a)).2

theorem famSpan_Rder' : ∀ F ∈ famSpan θ V τ κ 𝒟, ∀ τ', ∀ X ∈ lieAt V τ',
    (fun k => Rder θ V τ' X (F k)) ∈ famSpan θ V τ κ 𝒟 := by
  intro F hF τ' X hX
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hx
    exact famSpan_Rder_gen' hθ hκ hU h𝒟 hR hc hψ τ' hX
  | zero =>
    have e : (fun k => Rder θ V τ' X ((0 : K → GA D V → ℂ) k)) = 0 := by
      funext k g
      simp [Rder]
    rw [e]
    exact zero_mem _
  | add x y hx' hy' hx hy =>
    have sx := famSpan_sm' hθ hU h𝒟 x hx'
    have sy := famSpan_sm' hθ hU h𝒟 y hy'
    have e : (fun k => Rder θ V τ' X ((x + y) k)) = (fun k => Rder θ V τ' X (x k)) + fun k => Rder θ V τ' X (y k) := by
      funext k
      exact Rder_add (sx k) (sy k) hX
    rw [e]
    exact add_mem hx hy
  | smul a x _ hx =>
    have e : (fun k => Rder θ V τ' X ((a • x) k)) = a • fun k => Rder θ V τ' X (x k) := by
      funext k
      exact Rder_smul a (x k) τ' X
    rw [e]
    exact Submodule.smul_mem _ a hx

end Der

end GlobalTheory.KAvgApprox

namespace GlobalTheory.KAvgApprox

open GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate GlobalTheory.RealAverage

variable {D : D7} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau}
  {K : Type} [TopologicalSpace K] {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem famSpan_rapid [CompactSpace K] (hθ : IsInfFam θ) (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {𝒟 : Set (GA D V → ℂ)} (h𝒟 : ∀ ψ ∈ 𝒟, RapidDec V ψ) :
    ∀ F ∈ famSpan θ V τ κ 𝒟, (∀ k, ∀ γ ∈ GQ V, ∀ x, F k (γ * x) = F k x) ∧
      ∀ N : ℕ, ∃ C : ℝ, ∀ k x, ‖F k x‖ * quotHeight V x ^ N ≤ C := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hF
    refine ⟨fun k γ hγ x => by simp only [mul_assoc, (h𝒟 ψ hψ).left hγ], fun N => ?_⟩
    obtain ⟨Cψ, hCψ⟩ := (h𝒟 ψ hψ).decay N
    obtain ⟨Mc, hMc⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    obtain ⟨H, hH⟩ := isCompact_univ.exists_bound_of_continuousOn
      ((continuous_height V).comp (continuous_atTau hθ hκ hU)).continuousOn
    have hHk : ∀ k, height V (atTau θ V τ (κ k)) ≤ H := fun k => (le_abs_self _).trans (by
      simpa [Real.norm_eq_abs] using hH k (Set.mem_univ k))
    refine ⟨|Mc| * (|Cψ| * |H| ^ N), fun k x => ?_⟩
    set a := atTau θ V τ (κ k)
    have hq : quotHeight V x ≤ quotHeight V (x * a) * H := by
      have h1 := quotHeight_mul_le V (x * a) a⁻¹
      rw [mul_inv_cancel_right, height_inv] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hHk k) (quotHeight_pos V _).le)
    have hq' : quotHeight V x ^ N ≤ quotHeight V (x * a) ^ N * |H| ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (quotHeight_pos V x).le (hq.trans (mul_le_mul_of_nonneg_left (le_abs_self _)
        (quotHeight_pos V _).le)) N
    have h1 : ‖c k‖ ≤ |Mc| := (hMc k (Set.mem_univ k)).trans (le_abs_self _)
    have h2 : ‖ψ (x * a)‖ * quotHeight V (x * a) ^ N ≤ |Cψ| := (hCψ _).trans (le_abs_self _)
    calc ‖c k * ψ (x * a)‖ * quotHeight V x ^ N = ‖c k‖ * (‖ψ (x * a)‖ * quotHeight V x ^ N) := by
          rw [norm_mul, mul_assoc]
      _ ≤ |Mc| * (|Cψ| * |H| ^ N) := by
          refine mul_le_mul h1 ?_ (mul_nonneg (norm_nonneg _) (pow_nonneg (quotHeight_pos V x).le N)) (abs_nonneg _)
          calc ‖ψ (x * a)‖ * quotHeight V x ^ N ≤ ‖ψ (x * a)‖ * (quotHeight V (x * a) ^ N * |H| ^ N) :=
                mul_le_mul_of_nonneg_left hq' (norm_nonneg _)
            _ = (‖ψ (x * a)‖ * quotHeight V (x * a) ^ N) * |H| ^ N := by ring
            _ ≤ |Cψ| * |H| ^ N := mul_le_mul_of_nonneg_right h2 (by positivity)
  | zero => exact ⟨fun _ _ _ _ => rfl, fun N => ⟨0, fun k x => by simp⟩⟩
  | add F G _ _ hF hG =>
    refine ⟨fun k γ hγ x => by simp only [Pi.add_apply, hF.1 k γ hγ x, hG.1 k γ hγ x], fun N => ?_⟩
    obtain ⟨C1, hC1⟩ := hF.2 N
    obtain ⟨C2, hC2⟩ := hG.2 N
    refine ⟨C1 + C2, fun k x => ?_⟩
    have h0 := pow_nonneg (quotHeight_pos V x).le N
    calc ‖(F + G) k x‖ * quotHeight V x ^ N ≤ (‖F k x‖ + ‖G k x‖) * quotHeight V x ^ N :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) h0
      _ = ‖F k x‖ * quotHeight V x ^ N + ‖G k x‖ * quotHeight V x ^ N := add_mul _ _ _
      _ ≤ C1 + C2 := add_le_add (hC1 k x) (hC2 k x)
  | smul a F _ hF =>
    refine ⟨fun k γ hγ x => by simp only [Pi.smul_apply, hF.1 k γ hγ x], fun N => ?_⟩
    obtain ⟨C, hC⟩ := hF.2 N
    refine ⟨‖a‖ * C, fun k x => ?_⟩
    rw [Pi.smul_apply, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC k x) (norm_nonneg a)

end GlobalTheory.KAvgApprox

namespace GlobalTheory.KAvgApprox

open Formalism.REAL GlobalTheory.TypeSum GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate GlobalTheory.RealAverage

theorem rapidDec_avg_famSpan {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {ε : Fin V.rank → Bool}
    {κ : KG ε → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {𝒟 : Set (GA D V → ℂ)}
    (h𝒟 : ∀ ψ ∈ 𝒟, RapidDec V ψ ∧ ψ ∈ SmFun θ V) {G : KG ε → GA D V → ℂ} (hG : G ∈ famSpan θ V τ κ 𝒟) :
    RapidDec V (fun x => ∫ k, G k x ∂(muK ε)) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds V.rank ε).1
  obtain ⟨hl, hd⟩ := famSpan_rapid hθ hκ hU (fun ψ h => (h𝒟 ψ h).1) G hG
  refine ⟨fun γ hγ x => by simp only [hl _ γ hγ x], GlobalTheory.AvgFam.continuous_avg (muK ε)
    (famSpan_cont' hθ hκ hU (fun ψ h => ⟨(h𝒟 ψ h).1.continuous, (h𝒟 ψ h).2⟩) G hG), fun N => ?_⟩
  obtain ⟨C, hC⟩ := hd N
  refine ⟨C, fun x => ?_⟩
  have hp := pow_pos (quotHeight_pos V x) N
  have hb : ∀ k, ‖G k x‖ ≤ C / quotHeight V x ^ N := fun k => (le_div_iff₀ hp).2 (hC k x)
  have h1 := norm_integral_le_of_norm_le_const (μ := muK ε) (Filter.Eventually.of_forall hb)
  simp only [probReal_univ, mul_one] at h1
  exact (le_div_iff₀ hp).1 h1

theorem avg_rapid : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ → ∀ e : Formalism.REAL.KG ε → ℂ, Continuous e → ∀ f : GA D V → ℂ, GlobalTheory.Size.RapidDecSm θ V f → GlobalTheory.Size.RapidDecSm θ V (GlobalTheory.SeriesToClosure.avg θ V τ ε P e f) := by
  intro D θ hθ V τ ε P hP hJ e he f hf
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds V.rank ε).1
  set κ : KG ε → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun k => P⁻¹ * toMK k * P with hκdef
  have hκ : Continuous κ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := ε) (P := P)
  have hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun k =>
    GlobalTheory.LowTypeDetermined.conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  set 𝒟 : Set (GA D V → ℂ) := {ψ | GlobalTheory.Size.RapidDecSm θ V ψ}
  have h𝒟 : ∀ ψ ∈ 𝒟, Continuous ψ ∧ ψ ∈ SmFun θ V := fun ψ h => ⟨h.cont, h.smooth⟩
  have h𝒟' : ∀ ψ ∈ 𝒟, RapidDec V ψ ∧ ψ ∈ SmFun θ V := fun ψ h => ⟨h.rapidDec, h.smooth⟩
  have hR : ∀ ψ ∈ 𝒟, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ 𝒟 := fun ψ h τ' X hX => h.rder hX
  set F0 : KG ε → GA D V → ℂ := fun k x => e k * f (x * atTau θ V τ (κ k))
  have hF0 : F0 ∈ famSpan θ V τ κ 𝒟 := Submodule.subset_span ⟨e, he, f, hf, rfl⟩
  have FAM := GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives D θ hθ V (KG ε) (muK ε) (famSpan θ V τ κ 𝒟) (famSpan_cont' hθ hκ hU h𝒟)
    (famSpan_sm' hθ hU h𝒟) (famSpan_Rder' hθ hκ hU h𝒟 hR) F0 hF0
  have hwords : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      (fun k => l.foldr (fun p g => Rder θ V p.1 p.2 g) (F0 k)) ∈ famSpan θ V τ κ 𝒟 := by
    intro l hl
    induction l with
    | nil => exact hF0
    | cons p l ih =>
      exact famSpan_Rder' hθ hκ hU h𝒟 hR _ (ih fun q hq => hl q (List.mem_cons_of_mem _ hq)) p.1 p.2
        (hl p List.mem_cons_self)
  have hA : GlobalTheory.SeriesToClosure.avg θ V τ ε P e f = fun x => ∫ k, F0 k x ∂(muK ε) := rfl
  have h0 := rapidDec_avg_famSpan hθ hκ hU h𝒟' hF0
  rw [hA]
  refine { left := h0.1, level := ?_, cont := FAM.1, smooth := FAM.2.1, decay := fun l hl => ?_ }
  · obtain ⟨U, hUo, hk⟩ := hf.level
    refine ⟨U, hUo, fun u hu hfu g => ?_⟩
    show ∫ k, e k * f (g * u * atTau θ V τ (κ k)) ∂(muK ε) = ∫ k, e k * f (g * atTau θ V τ (κ k)) ∂(muK ε)
    congr 1
    funext k
    rw [mul_assoc, ← comm_of_mem V (atTau_mem (θ := θ) V τ (κ k)) hfu, ← mul_assoc, hk u hu hfu]
  · have e2 : GlobalTheory.Size.rWord θ V l (fun x => ∫ k, F0 k x ∂(muK ε)) =
        fun x => ∫ k, l.foldr (fun p g => Rder θ V p.1 p.2 g) (F0 k) x ∂(muK ε) := FAM.2.2.1 l hl
    rw [e2]
    exact rapidDec_avg_famSpan hθ hκ hU h𝒟' (hwords l hl)

end GlobalTheory.KAvgApprox

namespace GlobalTheory.KAvgApprox

open Formalism.REAL GlobalTheory.TypeSum GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate GlobalTheory.RealAverage

section FamGl

variable {D : D7} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {ε : Fin V.rank → Bool}
  {κ : KG ε → Matrix (Fin V.rank) (Fin V.rank) ℂ} {𝒟 : Set (GA D V → ℂ)}
  (hθ : IsInfFam θ) (hκ : Continuous κ) (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
  (h𝒟 : ∀ ψ ∈ 𝒟, Continuous ψ ∧ ψ ∈ SmFun θ V) (hR : ∀ ψ ∈ 𝒟, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ 𝒟)
include hθ hκ hU h𝒟 hR

theorem famSpan_glDer {F : KG ε → GA D V → ℂ} (hF : F ∈ famSpan θ V τ κ 𝒟)
    (a : D.what₂.Tau × Fin V.rank × Fin V.rank) :
    (fun k => GlobalTheory.Size.glDer θ V a (F k)) ∈ famSpan θ V τ κ 𝒟 ∧
      GlobalTheory.Size.glDer θ V a (fun x => ∫ k, F k x ∂(muK ε)) = fun x => ∫ k, GlobalTheory.Size.glDer θ V a (F k) x ∂(muK ε) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds V.rank ε).1
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V a.1 (Matrix.single a.2.1 a.2.2 1)
  have m1 := famSpan_Rder' hθ hκ hU h𝒟 hR F hF a.1 _ h1
  have m2 := famSpan_Rder' hθ hκ hU h𝒟 hR F hF a.1 _ h2
  have FAM := GlobalTheory.T.compactAverage_smoothFamily_closedUnderDerivatives D θ hθ V (KG ε) (muK ε) (famSpan θ V τ κ 𝒟) (famSpan_cont' hθ hκ hU h𝒟)
    (famSpan_sm' hθ hU h𝒟) (famSpan_Rder' hθ hκ hU h𝒟 hR) F hF
  have r1 := FAM.2.2.1 [(a.1, (1 / 2 : ℂ) • (Matrix.single a.2.1 a.2.2 1 + conjAt V a.1 (Matrix.single a.2.1 a.2.2 1)))]
    (fun p hp => by rw [List.mem_singleton.1 hp]; exact h1)
  have r2 := FAM.2.2.1 [(a.1, (1 / (2 * Complex.I) : ℂ) • (Matrix.single a.2.1 a.2.2 1 - conjAt V a.1 (Matrix.single a.2.1 a.2.2 1)))]
    (fun p hp => by rw [List.mem_singleton.1 hp]; exact h2)
  simp only [List.foldr_cons, List.foldr_nil] at r1 r2
  have i1 : ∀ x, Integrable (fun k => Rder θ V a.1 ((1 / 2 : ℂ) • (Matrix.single a.2.1 a.2.2 1 +
      conjAt V a.1 (Matrix.single a.2.1 a.2.2 1))) (F k) x) (muK ε) := fun x =>
    GlobalTheory.AvgFam.integrable_of_continuous (muK ε)
      ((famSpan_cont' hθ hκ hU h𝒟 _ m1).comp (continuous_id.prodMk continuous_const))
  have i2 : ∀ x, Integrable (fun k => Rder θ V a.1 ((1 / (2 * Complex.I) : ℂ) • (Matrix.single a.2.1 a.2.2 1 -
      conjAt V a.1 (Matrix.single a.2.1 a.2.2 1))) (F k) x) (muK ε) := fun x =>
    GlobalTheory.AvgFam.integrable_of_continuous (muK ε)
      ((famSpan_cont' hθ hκ hU h𝒟 _ m2).comp (continuous_id.prodMk continuous_const))
  refine ⟨add_mem m1 (Submodule.smul_mem _ Complex.I m2), ?_⟩
  show RderC θ V a.1 _ (fun x => ∫ k, F k x ∂(muK ε)) = fun x => ∫ k, RderC θ V a.1 _ (F k) x ∂(muK ε)
  simp only [RderC]
  rw [r1, r2]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add (i1 x) ((i2 x).const_mul _), integral_const_mul]

theorem famSpan_glWord {F : KG ε → GA D V → ℂ} (hF : F ∈ famSpan θ V τ κ 𝒟)
    (w : List (D.what₂.Tau × Fin V.rank × Fin V.rank)) :
    (fun k => GlobalTheory.Size.wordAct (GlobalTheory.Size.glDer θ V) w (F k)) ∈ famSpan θ V τ κ 𝒟 ∧
      GlobalTheory.Size.wordAct (GlobalTheory.Size.glDer θ V) w (fun x => ∫ k, F k x ∂(muK ε)) =
        fun x => ∫ k, GlobalTheory.Size.wordAct (GlobalTheory.Size.glDer θ V) w (F k) x ∂(muK ε) := by
  induction w with
  | nil => exact ⟨hF, rfl⟩
  | cons a w ih =>
    obtain ⟨m, e⟩ := ih
    have := famSpan_glDer hθ hκ hU h𝒟 hR m a
    simp only [GlobalTheory.Size.wordAct_cons]
    rw [e]
    exact this

end FamGl

theorem famSpan_equi {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {ε : Fin V.rank → Bool}
    {κ : KG ε → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hκ : Continuous κ)
    (hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {𝒟 : Set (GA D V → ℂ)} (h𝒟 : ∀ ψ ∈ 𝒟, RapidDec V ψ)
    {F : KG ε → GA D V → ℂ} (hF : F ∈ famSpan θ V τ κ 𝒟) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ k in 𝓝 (1 : KG ε), ∀ x, ‖F k x - F 1 x‖ < δ := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨c, hc, ψ, hψ, rfl⟩ := hF
    intro δ hδ
    obtain ⟨M, hM⟩ := (h𝒟 ψ hψ).bounded
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
    have h1 : ∀ᶠ k in 𝓝 (1 : KG ε), ‖c k - c 1‖ < δ / (2 * (M + 1)) := by
      have ht := ((hc.tendsto 1).sub_const (c 1)).norm
      simp only [sub_self, norm_zero] at ht
      exact ht.eventually (gt_mem_nhds (by positivity))
    have h2 := unif_right D V ψ (h𝒟 ψ hψ) (KG ε) (fun k => atTau θ V τ (κ k)) (continuous_atTau hθ hκ hU) 1
      (δ / (2 * (‖c 1‖ + 1))) (by positivity)
    filter_upwards [h1, h2] with k hk1 hk2 x
    have e : c k * ψ (x * atTau θ V τ (κ k)) - c 1 * ψ (x * atTau θ V τ (κ 1)) =
        (c k - c 1) * ψ (x * atTau θ V τ (κ k)) + c 1 * (ψ (x * atTau θ V τ (κ k)) - ψ (x * atTau θ V τ (κ 1))) := by
      ring
    rw [e]
    have b1 : ‖(c k - c 1) * ψ (x * atTau θ V τ (κ k))‖ ≤ δ / (2 * (M + 1)) * M := by
      rw [norm_mul]; exact mul_le_mul hk1.le (hM _) (norm_nonneg _) (by positivity)
    have b2 : ‖c 1 * (ψ (x * atTau θ V τ (κ k)) - ψ (x * atTau θ V τ (κ 1)))‖ ≤
        ‖c 1‖ * (δ / (2 * (‖c 1‖ + 1))) := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hk2 x).le (norm_nonneg _)
    have b3 : δ / (2 * (M + 1)) * M < δ / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have b4 : ‖c 1‖ * (δ / (2 * (‖c 1‖ + 1))) < δ / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [norm_nonneg (c 1)]
    calc _ ≤ _ := norm_add_le _ _
      _ < δ := by linarith
  | zero => exact fun δ hδ => Filter.Eventually.of_forall fun k x => by simpa using hδ
  | add F G _ _ hF hG =>
    intro δ hδ
    filter_upwards [hF (δ / 2) (half_pos hδ), hG (δ / 2) (half_pos hδ)] with k h1 h2 x
    have e : (F + G) k x - (F + G) 1 x = (F k x - F 1 x) + (G k x - G 1 x) := by
      simp only [Pi.add_apply]; ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ < δ := by linarith [h1 x, h2 x]
  | smul a F _ hF =>
    intro δ hδ
    filter_upwards [hF (δ / (‖a‖ + 1)) (by positivity)] with k h1 x
    have e : (a • F) k x - (a • F) 1 x = a * (F k x - F 1 x) := by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e, norm_mul]
    calc ‖a‖ * ‖F k x - F 1 x‖ ≤ ‖a‖ * (δ / (‖a‖ + 1)) := mul_le_mul_of_nonneg_left (h1 x).le (norm_nonneg _)
      _ < δ := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg a]

theorem family : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ → ∀ f : GA D V → ℂ, GlobalTheory.Size.RapidDecSm θ V f → ∀ w : List (D.what₂.Tau × Fin V.rank × Fin V.rank), ∃ G : Formalism.REAL.KG ε → GA D V → ℂ, (∀ x, Continuous fun k => G k x) ∧ (∃ M : ℝ, ∀ k x, ‖G k x‖ ≤ M) ∧ (∀ δ : ℝ, 0 < δ → ∀ᶠ k in nhds (1 : Formalism.REAL.KG ε), ∀ x, ‖G k x - G 1 x‖ < δ) ∧ G 1 = GlobalTheory.Size.wordAct (GlobalTheory.Size.glDer θ V) w f ∧ ∀ e : Formalism.REAL.KG ε → ℂ, Continuous e → GlobalTheory.Size.wordAct (GlobalTheory.Size.glDer θ V) w (GlobalTheory.SeriesToClosure.avg θ V τ ε P e f) = fun x => ∫ k, e k * G k x ∂(Formalism.REAL.muK ε) := by
  intro D θ hθ V τ ε P hP hJ f hf w
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds V.rank ε).1
  set κ : KG ε → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun k => P⁻¹ * toMK k * P with hκdef
  have hκ : Continuous κ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := ε) (P := P)
  have hU : ∀ k, κ k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun k =>
    GlobalTheory.LowTypeDetermined.conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  set 𝒟 : Set (GA D V → ℂ) := {ψ | GlobalTheory.Size.RapidDecSm θ V ψ}
  have h𝒟 : ∀ ψ ∈ 𝒟, Continuous ψ ∧ ψ ∈ SmFun θ V := fun ψ h => ⟨h.cont, h.smooth⟩
  have h𝒟r : ∀ ψ ∈ 𝒟, RapidDec V ψ := fun ψ h => h.rapidDec
  have hR : ∀ ψ ∈ 𝒟, ∀ τ' X, X ∈ lieAt V τ' → Rder θ V τ' X ψ ∈ 𝒟 := fun ψ h τ' X hX => h.rder hX
  set Fr : KG ε → GA D V → ℂ := fun k x => (fun _ => (1 : ℂ)) k * f (x * atTau θ V τ (κ k))
  have hFr : Fr ∈ famSpan θ V τ κ 𝒟 := Submodule.subset_span ⟨fun _ => 1, continuous_const, f, hf, rfl⟩
  obtain ⟨hGm, -⟩ := famSpan_glWord hθ hκ hU h𝒟 hR hFr w
  set G : KG ε → GA D V → ℂ := fun k => GlobalTheory.Size.wordAct (GlobalTheory.Size.glDer θ V) w (Fr k) with hGdef
  have hκ1 : atTau θ V τ (κ 1) = 1 := by
    have : κ 1 = 1 := by
      show P⁻¹ * 1 * P = 1
      rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]
    rw [this, GlobalTheory.PointAtPlaceHom.atTau_one hθ]
  have hFr1 : Fr 1 = f := by
    funext x
    simp only [Fr, hκ1, mul_one, one_mul]
  clear_value G
  obtain ⟨C, hC⟩ := (famSpan_rapid hθ hκ hU h𝒟r G hGm).2 0
  have c1 : ∀ x, Continuous fun k => G k x := fun x =>
    (famSpan_cont' hθ hκ hU h𝒟 G hGm).comp (continuous_id.prodMk continuous_const)
  have c2 : ∀ k x, ‖G k x‖ ≤ C := fun k x => by
    have := hC k x
    rwa [pow_zero, mul_one] at this
  have c3 := famSpan_equi hθ hκ hU h𝒟r hGm
  have c4 : G 1 = GlobalTheory.Size.wordAct (GlobalTheory.Size.glDer θ V) w f := by
    rw [hGdef]
    show GlobalTheory.Size.wordAct (GlobalTheory.Size.glDer θ V) w (Fr 1) = _
    rw [hFr1]
  refine ⟨G, c1, ⟨C, c2⟩, c3, c4, fun e he => ?_⟩
  set F0 : KG ε → GA D V → ℂ := fun k x => e k * f (x * atTau θ V τ (κ k))
  have hF0 : F0 ∈ famSpan θ V τ κ 𝒟 := Submodule.subset_span ⟨e, he, f, hf, rfl⟩
  have hA : GlobalTheory.SeriesToClosure.avg θ V τ ε P e f = fun x => ∫ k, F0 k x ∂(muK ε) := rfl
  rw [hA, (famSpan_glWord hθ hκ hU h𝒟 hR hF0 w).2]
  funext x
  congr 1
  funext k
  have e1 : F0 k = e k • Fr k := by
    funext y
    simp only [F0, Fr, Pi.smul_apply, smul_eq_mul, one_mul]
  rw [e1, (GlobalTheory.Size.linOnSm_glWord (θ := θ) (V := V) w).smul, hGdef]
  rfl

end GlobalTheory.KAvgApprox

namespace GlobalTheory.KAvgApprox
open Formalism.REAL GlobalTheory.TypeSum

theorem one_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ → ∀ f : GA D V → ℂ, GlobalTheory.Size.RapidDecSm θ V f → ∀ (d : ℕ) (η : ℝ), 0 < η → ∃ e : KG ε → ℂ, KFinFun ε e ∧ GlobalTheory.Size.growthSob θ V d 0 (f - GlobalTheory.SeriesToClosure.avg θ V τ ε P e f) ≤ ENNReal.ofReal η := by
  intro D θ hθ V τ ε P hP hJ f hf d η hη
  set α := D.what₂.Tau × Fin V.rank × Fin V.rank
  choose G hGc hGb hGe hG1 hGa using fun w => family D θ hθ V τ ε P hP hJ f hf w
  set ι := Σ k : Fin (d + 1), (Fin k → α)
  set cnt : ℕ := Fintype.card ι
  set δ : ℝ := η / (cnt + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  choose M hM using fun w => hGb w
  obtain ⟨e, he, hap⟩ := approx_family V.rank ε (ι × GA D V) (fun p k => G (List.ofFn p.1.2) k p.2)
    (fun p => hGc _ p.2) ⟨∑ i : ι, |M (List.ofFn i.2)|, fun p k => (hM _ k p.2).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i : ι => |M (List.ofFn i.2)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ p.1)))⟩
    (fun δ' hδ' => (Filter.eventually_all.2 fun i : ι => hGe (List.ofFn i.2) δ' hδ').mono fun k hk p => hk p.1 p.2)
    δ hδ0
  have hec : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hAs := (avg_rapid D θ hθ V τ ε P hP hJ e hec f hf).smooth
  refine ⟨e, he, ?_⟩
  have hterm : ∀ w : List α, (∃ i : ι, List.ofFn i.2 = w) →
      GlobalTheory.Size.growthSize V 0 (GlobalTheory.Size.wordAct (GlobalTheory.Size.glDer θ V) w (f - GlobalTheory.SeriesToClosure.avg θ V τ ε P e f))
        ≤ ENNReal.ofReal δ := by
    rintro w ⟨i, rfl⟩
    have hlin := GlobalTheory.Size.linOnSm_glWord (θ := θ) (V := V) (List.ofFn i.2)
    have e1 : f - GlobalTheory.SeriesToClosure.avg θ V τ ε P e f = f + (-1 : ℂ) • GlobalTheory.SeriesToClosure.avg θ V τ ε P e f := by
      rw [neg_one_smul, sub_eq_add_neg]
    rw [e1, hlin.add _ hf.smooth _ ((GlobalTheory.Mem.AutSpace.SmFun θ V).smul_mem _ hAs), hlin.smul, hGa _ e hec, ← hG1]
    refine (GlobalTheory.Size.growthSize_le_iff hδ0.le).2 fun x => ?_
    have := hap (i, x)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_zero, mul_one]
    simpa [sub_eq_add_neg] using this
  calc GlobalTheory.Size.growthSob θ V d 0 (f - GlobalTheory.SeriesToClosure.avg θ V τ ε P e f)
        ≤ ∑ k ∈ Finset.range (d + 1), ∑ a : Fin k → α, ENNReal.ofReal δ := by
        unfold GlobalTheory.Size.growthSob GlobalTheory.Size.wordSum
        exact Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun a _ =>
          hterm _ ⟨⟨⟨k, Finset.mem_range.1 hk⟩, a⟩, rfl⟩
    _ = (cnt : ℝ≥0∞) * ENNReal.ofReal δ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Finset.sum_mul]
        congr 1
        simp only [cnt, ι, Fintype.card_sigma]
        push_cast
        exact (Fin.sum_univ_eq_sum_range (fun k => ((Fintype.card (Fin k → α) : ℕ) : ℝ≥0∞)) (d + 1)).symm
    _ ≤ ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [hδ, mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

end GlobalTheory.KAvgApprox

namespace GlobalTheory.KAvgApprox
open Formalism.REAL GlobalTheory.TypeSum

theorem avgList_congr {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D) {e e' : ∀ τ, KG (N.M.ε τ) → ℂ}
    (l : List D.what₂.Tau) (h : ∀ τ ∈ l, e τ = e' τ) (φ : GA D N.V → ℂ) :
    GlobalTheory.CuspApproxAll.avgList θ N e l φ = GlobalTheory.CuspApproxAll.avgList θ N e' l φ := by
  induction l with
  | nil => rfl
  | cons τ l ih =>
    rw [GlobalTheory.CuspApproxAll.avgList_cons, GlobalTheory.CuspApproxAll.avgList_cons, h τ List.mem_cons_self,
      ih fun τ' hτ' => h τ' (List.mem_cons_of_mem _ hτ')]

theorem avgList_rapid {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (N : GlobalTheory.Grid.Node D) (e : ∀ τ, KG (N.M.ε τ) → ℂ)
    (he : ∀ τ, Continuous (e τ)) (l : List D.what₂.Tau) {φ : GA D N.V → ℂ} (hφ : GlobalTheory.Size.RapidDecSm θ N.V φ) :
    GlobalTheory.Size.RapidDecSm θ N.V (GlobalTheory.CuspApproxAll.avgList θ N e l φ) := by
  induction l with
  | nil => exact hφ
  | cons τ l ih =>
    rw [GlobalTheory.CuspApproxAll.avgList_cons]
    exact avg_rapid D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) (e τ) (he τ) _ ih

theorem kFinFun_zero {n : ℕ} (ε : Fin n → Bool) : KFinFun ε (0 : KG ε → ℂ) :=
  ⟨⊥, inferInstance, zero_mem _, fun φ hφ => by rw [(Submodule.mem_bot ℂ).1 hφ]; exact continuous_const,
    fun φ hφ k₀ => by rw [(Submodule.mem_bot ℂ).1 hφ]; exact ⟨zero_mem _, zero_mem _⟩⟩

theorem approx_avgList : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.Size.RapidDecSm θ N.V φ → ∀ (l : List D.what₂.Tau), l.Nodup → ∀ (d : ℕ) (η : ℝ), 0 < η → ∃ e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ, (∀ τ, GlobalTheory.TypeSum.KFinFun (N.M.ε τ) (e τ)) ∧ GlobalTheory.Size.growthSob θ N.V d 0 (φ - GlobalTheory.CuspApproxAll.avgList θ N e l φ) ≤ ENNReal.ofReal η := by
  intro D θ hθ N φ hφ l hl d η hη
  classical
  have hcont : ∀ τ (e : KG (N.M.ε τ) → ℂ), KFinFun (N.M.ε τ) e → Continuous e := fun τ e he => by
    obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  induction l generalizing η with
  | nil =>
    refine ⟨fun τ => 0, fun τ => kFinFun_zero _, ?_⟩
    rw [GlobalTheory.CuspApproxAll.avgList_nil, sub_self]
    have h0 := GlobalTheory.Size.growthSob_smul (θ := θ) (V := N.V) (φ := 0) (0 : ℂ) d 0
    rw [zero_smul, enorm_zero, zero_mul] at h0
    rw [h0]
    exact zero_le
  | cons τ l ih =>
    obtain ⟨hτ, hl'⟩ := List.nodup_cons.1 hl
    obtain ⟨e, he, h1⟩ := ih hl' (η / 2) (half_pos hη)
    have hg := avgList_rapid hθ N e (fun τ => hcont τ _ (he τ)) l hφ
    obtain ⟨e₀, he₀, h2⟩ := one_place D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) _ hg d
      (η / 2) (half_pos hη)
    have hA := avg_rapid D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) e₀ (hcont τ _ he₀) _ hg
    refine ⟨Function.update e τ e₀, fun τ' => ?_, ?_⟩
    · by_cases h : τ' = τ
      · subst h; simpa using he₀
      · rw [Function.update_of_ne h]; exact he τ'
    · have hl2 : GlobalTheory.CuspApproxAll.avgList θ N (Function.update e τ e₀) l φ = GlobalTheory.CuspApproxAll.avgList θ N e l φ :=
        avgList_congr θ N l (fun τ' hτ' => Function.update_of_ne (by rintro rfl; exact hτ hτ') _ _) φ
      rw [GlobalTheory.CuspApproxAll.avgList_cons, hl2, Function.update_self]
      set g := GlobalTheory.CuspApproxAll.avgList θ N e l φ
      have e1 : φ - GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e₀ g =
          (φ - g) + (g - GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e₀ g) := by abel
      rw [e1]
      refine (GlobalTheory.Size.growthSob_add_le (sub_mem hφ.smooth hg.smooth) (sub_mem hg.smooth hA.smooth) d 0).trans ?_
      calc _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add h1 h2
        _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_add (half_pos hη).le (half_pos hη).le, add_halves]

end GlobalTheory.KAvgApprox
