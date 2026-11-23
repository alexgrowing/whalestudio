import Formalism.HermitianCurvature.StatementLE
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem mulF_rpow_zero (B : Base) {A : Type} (u : Fn B A) : mulF B (fun x => x ^ (0:ℝ)) u = u := by
  funext ω a; simp [mulF]

theorem dS_zero (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) : dS B T u 0 = T u := by
  funext ω a
  have h1 : mulF B (fun _ => (1:ℝ)) u = u := by funext ω a; simp [mulF]
  simp [dS, conjS, h1]

theorem pr_self (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) (ω : B.Ω) :
    pr B wt v v ω = ((LE.sq B wt v ω : ℝ) : ℂ) := by
  simp only [pr, LE.sq, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]; simp

theorem int_pr_self (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) :
    ∫ ω, pr B wt v v ω ∂B.μ = ((∫ ω, LE.sq B wt v ω ∂B.μ : ℝ) : ℂ) := by
  simp_rw [pr_self]; exact integral_ofReal

theorem smoothLog_sc (c : Cut) (ε : ℝ) (m : ℕ) : SmoothLog (c.sc ε m) := by
  unfold SmoothLog Cut.sc
  exact (c.smooth.comp (Real.contDiff_exp.div_const ε)).pow m

theorem meas_ld (p : ℕ) (φ : ℝ → ℝ) (h : SmoothLog φ) : Measurable (ld p φ) := by
  unfold ld
  have : Continuous (iteratedDeriv p (fun u : ℝ => φ (Real.exp u))) :=
    h.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  exact this.measurable.comp Real.measurable_log

theorem measurable_apply_mulF_of_jetLocal (hLeib : Leibniz) (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) (M : ℕ)
    (hJ : JetLocal B T u) (hP : PolyS B T u M) (hm : ∀ p a, Measurable fun ω => dS B T u p ω a)
    (φ : ℝ → ℝ) (hφ : SmoothLog φ) (a : A') : Measurable fun ω => T (mulF B φ u) ω a := by
  have := hLeib B A A' T u M hJ hP φ hφ
  simp_rw [this]
  refine Finset.measurable_sum _ fun p _ => ?_
  refine Measurable.div_const (Measurable.mul ?_ (hm p a)) _
  exact Complex.measurable_ofReal.comp ((meas_ld p φ hφ).comp B.G_meas)

theorem lemmaEprimeFromSteps : LemmaEprimeFromSteps := by
  intro hLeib hCut hL2 hPair h5 h6 B X c M hpos hMeas hJet hPoly hCoef hPol hLoc hBeta
  obtain ⟨hmu, hmC, hmd, hmS⟩ := hMeas
  have hI0 : Integrable (LE.sq B X.dw (X.gw X.u)) B.μ := by
    have := hCoef 0; rwa [dS_zero] at this
  have hmg : ∀ a, Measurable fun ω => X.gw X.u ω a := by
    intro a; have := hmS 0 a; rwa [dS_zero] at this
  have L1 := hL2 hLeib hCut B X.R X.ι X.gw X.u X.dw c M 1 le_rfl hpos hmd hJet hPoly hmS hCoef
  have L2 := hL2 hLeib hCut B X.R X.ι X.gw X.u X.dw c M 2 (by norm_num) hpos hmd hJet hPoly hmS hCoef
  have hmT : ∀ (m : ℕ) (ε : ℝ) (a : X.ι), Measurable fun ω => X.gw (mulF B (c.sc ε m) X.u) ω a :=
    fun m ε a => measurable_apply_mulF_of_jetLocal hLeib B X.gw X.u M hJet hPoly hmS _ (smoothLog_sc c ε m) a
  have hzero : Tendsto (fun ε : ℝ => ∫ ω, LE.sq B X.dw (fun ω a => X.gw X.u ω a - X.gw X.u ω a) ω ∂B.μ)
      (𝓝[>] 0) (𝓝 0) := by
    simp [LE.sq]

  have P2 := hPair B X.ι X.dw (X.gw X.u) (X.gw X.u) (fun _ => X.gw X.u) (fun ε => X.gw (mulF B (c.sc ε 2) X.u))
    hpos hmd hmg hmg (fun _ a _ => hmg a) (fun ε a _ => hmT 2 ε a) hI0 hI0 (fun _ _ => hI0) L2.1 hzero L2.2
  have T5 := h5 B X c ⟨hmu, hmC, hmd, hmS⟩ hBeta
  have hev : (fun ε : ℝ => X.beta (X.Cw X.u) (mulF B (c.sc ε 2) X.u)) =ᶠ[𝓝[>] 0]
      fun ε : ℝ => ∫ ω, pr B X.dw (X.gw X.u) (X.gw (mulF B (c.sc ε 2) X.u)) ω ∂B.μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact h6 hCut B X c hJet hPol hLoc ε hε
  have heq : ∫ ω, pr B X.dw (X.gw X.u) (X.gw X.u) ω ∂B.μ = X.beta (X.Cw X.u) X.u :=
    tendsto_nhds_unique P2 (T5.congr' hev)
  refine ⟨hI0, ?_, ?_⟩
  · rw [← int_pr_self]; exact heq
  · have P1 := hPair B X.ι X.dw (X.gw X.u) (X.gw X.u) (fun ε => X.gw (mulF B (c.sc ε 1) X.u))
      (fun ε => X.gw (mulF B (c.sc ε 1) X.u))
      hpos hmd hmg hmg (fun ε a _ => hmT 1 ε a) (fun ε a _ => hmT 1 ε a) hI0 hI0 L1.1 L1.1 L1.2 L1.2
    rw [heq] at P1
    refine P1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hPol ε ε 1 1 hε hε le_rfl le_rfl).symm

theorem ld_one (q : ℕ) (x : ℝ) : ld q (fun _ => (1:ℝ)) x = if q = 0 then 1 else 0 := by
  unfold ld
  cases q with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ']

theorem epStep6 : EpStep6 := by
  intro hCut B X c hJet hPol hLoc ε hε
  obtain ⟨m, cc, hc⟩ := hJet
  have hε1 : 0 < ε / 8 := by positivity
  have h1u : mulF B (fun _ => (1:ℝ)) X.u = X.u := by funext ω a; simp [mulF]
  have hbig : ∀ ω, ε / 8 < B.G ω → ∀ a, X.gw (mulF B (c.sc (ε/8) 1) X.u) ω a = X.gw X.u ω a := by
    intro ω hω a
    have e1 := hc (c.sc (ε/8) 1) (smoothLog_sc c _ 1) ω a
    have e2 := hc (fun _ => (1:ℝ)) (by unfold SmoothLog; exact contDiff_const) ω a
    rw [h1u] at e2
    rw [e1, e2]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨C, hC⟩ := hCut c 1 q le_rfl
    rw [(hC (ε/8) (B.G ω) hε1 (B.G_pos ω)).2.2 hω, ld_one]
  have hsmall : ∀ ω, B.G ω ≤ ε / 8 → ∀ a, X.gw (mulF B (c.sc ε 2) X.u) ω a = 0 := by
    intro ω hω a
    rw [hc (c.sc ε 2) (smoothLog_sc c _ 2) ω a]
    refine Finset.sum_eq_zero fun q _ => ?_
    obtain ⟨C, hC⟩ := hCut c 2 q (by norm_num)
    rw [(hC ε (B.G ω) hε (B.G_pos ω)).2.1 (by linarith)]; simp
  have hsc : ∀ ω, B.G ω ≤ ε / 8 → c.sc ε 2 (B.G ω) = 0 := by
    intro ω hω
    have : B.G ω / ε ≤ 1 / 2 := by rw [div_le_iff₀ hε]; linarith
    simp [Cut.sc, c.zero _ this]
  calc X.beta (X.Cw X.u) (mulF B (c.sc ε 2) X.u)
      = X.beta (X.Cw (mulF B (c.sc (ε/8) 1) X.u)) (mulF B (c.sc ε 2) X.u) := by
        unfold EP.beta
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [pr]
        refine Finset.sum_congr rfl fun a _ => ?_
        rcases lt_or_ge (ε/8) (B.G ω) with h | h
        · rw [hLoc (ε/8) ω hε1 h a]
        · simp [mulF, hsc ω h]
    _ = ∫ ω, pr B X.dw (X.gw (mulF B (c.sc (ε/8) 1) X.u)) (X.gw (mulF B (c.sc ε 2) X.u)) ω ∂B.μ :=
        hPol (ε/8) ε 1 2 hε1 hε le_rfl (by norm_num)
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [pr]
        refine Finset.sum_congr rfl fun a _ => ?_
        rcases lt_or_ge (ε/8) (B.G ω) with h | h
        · rw [hbig ω h a]
        · simp [hsmall ω h a]

theorem epCoefInt : EpCoefInt := by
  intro h B X p N hpN hpos hMeas hNF q
  obtain ⟨n, v, C, h1, h2, h3⟩ := hNF q
  obtain ⟨hmu, hmC, hmd, hmS⟩ := hMeas
  refine h B (Fin n) _ v C p N hpN ?_ ?_ h1 h2 h3
  · unfold LE.sq
    refine Finset.measurable_sum _ fun a _ => ?_
    exact (hmd a).mul ((hmS q a).norm.pow_const 2)
  · intro ω; unfold LE.sq
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hpos ω a) (by positivity)

open Polynomial in
theorem iterDeriv_poly (P : ℂ[X]) (p : ℕ) :
    iteratedDeriv p (fun s : ℝ => P.eval (s : ℂ)) = fun s : ℝ => ((derivative^[p]) P).eval (s : ℂ) := by
  induction p generalizing P with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have : deriv (fun s : ℝ => P.eval (s : ℂ)) = fun s : ℝ => (derivative P).eval (s : ℂ) := by
      funext s
      exact ((P.hasDerivAt (s : ℂ)).comp_ofReal).deriv
    rw [this, ih]
    simp [Function.iterate_succ]

open Polynomial in
noncomputable def mkP (m : ℕ) (c : ℕ → ℂ) : ℂ[X] := ∑ q ∈ range (m + 1), C (c q) * X ^ q

open Polynomial in
theorem mkP_eval (m : ℕ) (c : ℕ → ℂ) (z : ℂ) : (mkP m c).eval z = ∑ q ∈ range (m + 1), z ^ q * c q := by
  unfold mkP
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]

open Polynomial in
theorem mkP_coeff (m : ℕ) (c : ℕ → ℂ) (k : ℕ) : (mkP m c).coeff k = if k < m + 1 then c k else 0 := by
  simp [mkP, finsetSum_coeff, coeff_C_mul, coeff_X_pow]

theorem ld_rpow (q : ℕ) (s x : ℝ) (hx : 0 < x) : ld q (fun y => y ^ s) x = s ^ q * x ^ s := by
  unfold ld
  have : (fun u : ℝ => (Real.exp u) ^ s) = fun u : ℝ => Real.exp (s * u) := by
    funext u; rw [mul_comm, Real.exp_mul]
  rw [this, iteratedDeriv_exp_const_mul]
  show s ^ q * Real.exp (s * Real.log x) = _
  rw [mul_comm s, Real.exp_mul, Real.exp_log hx]

theorem smoothLog_rpow (s : ℝ) : SmoothLog (fun y => y ^ s) := by
  unfold SmoothLog
  have : (fun u : ℝ => (Real.exp u) ^ s) = fun u : ℝ => Real.exp (s * u) := by
    funext u; rw [mul_comm, Real.exp_mul]
  rw [this]
  exact Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)

open Polynomial in
theorem leibniz : Leibniz := by
  intro B A A' T u d hJ hP φ hφ ω a
  obtain ⟨m, c, hc⟩ := hJ
  obtain ⟨c', hc'⟩ := hP
  have hconj : ∀ s : ℝ, conjS B T u s ω a = (mkP m (fun q => c q ω a)).eval (s : ℂ) := by
    intro s
    rw [mkP_eval]
    unfold conjS
    rw [hc _ (smoothLog_rpow s) ω a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ld_rpow q s _ (B.G_pos ω)]
    have h1 : (B.G ω) ^ (-s) * (B.G ω) ^ s = 1 := by
      rw [← Real.rpow_add (B.G_pos ω)]; simp
    have h2 : (((B.G ω) ^ (-s) : ℝ) : ℂ) * (((B.G ω) ^ s : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, h1]; simp
    push_cast
    linear_combination ((s:ℂ) ^ q * c q ω a) * h2
  have hPP : mkP m (fun q => c q ω a) = mkP d (fun q => c' q ω a) := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono (s := Set.range (fun s : ℝ => (s : ℂ))) ?_
      (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro _ ⟨s, rfl⟩
    show _ = _
    rw [← hconj s, hc' s ω a, mkP_eval]
  have hdS : ∀ p, dS B T u p ω a = p.factorial * (mkP m (fun q => c q ω a)).coeff p := by
    intro p
    unfold dS
    simp_rw [hconj]
    rw [iterDeriv_poly]
    simp only [Complex.ofReal_zero]
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
    simp [Nat.descFactorial_self]
  rw [hc φ hφ ω a]
  have e1 : ∑ q ∈ range (m + 1), (ld q φ (B.G ω) : ℂ) * c q ω a =
      ∑ q ∈ range (max m d + 1), (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q := by
    have hs := Finset.sum_subset (s₁ := range (m+1)) (s₂ := range (max m d + 1))
      (f := fun q => (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q)
      (by intro q hq; simp only [Finset.mem_range] at *; omega)
      (by intro q _ hq; rw [mkP_coeff, if_neg (by simpa using hq)]; simp)
    rw [← hs]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [mkP_coeff, if_pos (Finset.mem_range.mp hq)]
  have e2 : ∑ p ∈ range (d + 1), (ld p φ (B.G ω) : ℂ) * dS B T u p ω a / p.factorial =
      ∑ q ∈ range (max m d + 1), (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q := by
    have hs := Finset.sum_subset (s₁ := range (d+1)) (s₂ := range (max m d + 1))
      (f := fun q => (ld q φ (B.G ω) : ℂ) * (mkP m (fun q => c q ω a)).coeff q)
      (by intro q hq; simp only [Finset.mem_range] at *; omega)
      (by intro q _ hq; rw [hPP, mkP_coeff, if_neg (by simpa using hq)]; simp)
    rw [← hs]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hdS]
    have : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
    field_simp
  rw [e1, e2]

theorem thetaForm : ThetaForm := by
  intro ε σ hε v
  unfold th
  have h1 : Real.exp v / (Real.exp v + ε) = (1 + ε * Real.exp (-v))⁻¹ := by
    rw [Real.exp_neg]; have := Real.exp_pos v; field_simp
  have h2 : 0 ≤ 1 + ε * Real.exp (-v) := by positivity
  rw [h1, Real.inv_rpow h2, Real.rpow_neg h2]

theorem thetaRange : ThetaRange := by
  intro ε σ x hε hσ hx
  unfold th
  have h0 : 0 < x / (x + ε) := by positivity
  have h1 : x / (x + ε) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  exact ⟨Real.rpow_pos_of_pos h0 σ, Real.rpow_le_one h0.le h1 hσ⟩

theorem pr_mulF (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (h u : Fn B A) (φ : ℝ → ℝ) (ω : B.Ω) :
    pr B wt h (mulF B φ u) ω = (φ (B.G ω) : ℂ) * pr B wt h u ω := by
  simp only [pr, mulF, Finset.mul_sum, map_mul, Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem epStep5 : EpStep5 := by
  intro B X c hMeas hBeta
  obtain ⟨hmu, hmC, hmd, hmS⟩ := hMeas
  obtain ⟨hIu, hIh⟩ := hBeta
  unfold EP.beta
  simp_rw [pr_mulF]
  have hmpr : Measurable fun ω => pr B (fun _ _ => (1:ℝ)) (X.Cw X.u) X.u ω := by
    unfold pr
    refine Finset.measurable_sum _ fun a _ => ?_
    exact (measurable_const.mul (hmC a)).mul (Complex.continuous_conj.measurable.comp (hmu a))
  have hbd : ∀ ω, ‖pr B (fun _ _ => (1:ℝ)) (X.Cw X.u) X.u ω‖ ≤
      LE.sq B (fun _ _ => 1) (X.Cw X.u) ω + LE.sq B (fun _ _ => 1) X.u ω := by
    intro ω
    unfold pr LE.sq
    rw [← Finset.sum_add_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    simp only [Complex.ofReal_one, one_mul, norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖X.Cw X.u ω a‖ - ‖X.u ω a‖), norm_nonneg (X.Cw X.u ω a), norm_nonneg (X.u ω a)]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ω => LE.sq B (fun _ _ => 1) (X.Cw X.u) ω + LE.sq B (fun _ _ => 1) X.u ω) ?_ ?_ (hIh.add hIu) ?_
  · refine Eventually.of_forall fun ε => ?_
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ hmpr)
    refine Complex.measurable_ofReal.comp ?_
    unfold Cut.sc
    exact ((c.smooth.continuous.measurable.comp (B.G_meas.div_const ε)).pow_const 2)
  · refine Eventually.of_forall fun ε => Eventually.of_forall fun ω => ?_
    rw [norm_mul]
    have h1 : ‖((c.sc ε 2 (B.G ω) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      unfold Cut.sc
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (c.nonneg _) (c.le_one _)
    calc _ ≤ 1 * ‖pr B (fun _ _ => (1:ℝ)) (X.Cw X.u) X.u ω‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hbd ω
  · refine Eventually.of_forall fun ω => ?_
    refine tendsto_const_nhds.congr' ?_
    have : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo 0 (B.G ω) := Ioo_mem_nhdsGT (B.G_pos ω)
    filter_upwards [this] with ε hε
    have h1 : 1 ≤ B.G ω / ε := by rw [le_div_iff₀ hε.1]; linarith [hε.2]
    simp [Cut.sc, c.one _ h1]

theorem derived_energy_L2 : WeightedIntegrable := by
  intro B T _ f v C p N hpN hmf hf0 hfb h1 h2
  have hg : Integrable (fun ω => |C| * ∑ t, (‖v t ω‖ ^ 2 + (B.G ω) ^ (2 * p) * ‖v t ω‖ ^ 2)) B.μ :=
    (integrable_finset_sum _ fun t _ => (h1 t).add (h2 t)).const_mul _
  refine hg.mono' hmf.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]
  refine (hfb ω).trans ?_
  have hG := B.G_pos ω
  have hexp : (0:ℝ) ≤ (2 * p : ℝ) - N := by
    have : (N:ℝ) ≤ 2 * p := by exact_mod_cast hpN
    linarith
  have hpow : (B.G ω) ^ ((2 * p : ℝ) - N) ≤ 1 + (B.G ω) ^ (2 * p) := by
    rcases le_total (B.G ω) 1 with h | h
    · have := Real.rpow_le_one hG.le h hexp
      have h' : 0 ≤ (B.G ω) ^ (2 * p) := by positivity
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h (show (2 * p : ℝ) - N ≤ ((2 * p : ℕ) : ℝ) by push_cast; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
      rw [Real.rpow_natCast] at this
      linarith
  have hS : 0 ≤ ∑ t, ‖v t ω‖ ^ 2 := Finset.sum_nonneg fun t _ => by positivity
  have hr : 0 ≤ (B.G ω) ^ ((2 * p : ℝ) - N) := Real.rpow_nonneg hG.le _
  calc C * (B.G ω) ^ ((2 * p : ℝ) - N) * ∑ t, ‖v t ω‖ ^ 2
      ≤ |C| * (B.G ω) ^ ((2 * p : ℝ) - N) * ∑ t, ‖v t ω‖ ^ 2 := by
        gcongr; exact le_abs_self C
    _ ≤ |C| * (1 + (B.G ω) ^ (2 * p)) * ∑ t, ‖v t ω‖ ^ 2 := by gcongr
    _ = _ := by
        rw [mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun t _ => ?_
        ring

theorem thetaSmooth : ThetaSmooth := by
  intro ε σ hε
  unfold SmoothLog
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  refine ContDiff.rpow_const_of_ne ?_ ?_
  · exact contDiff_const.add (contDiff_const.mul (Real.contDiff_exp.comp contDiff_neg))
  · intro u; positivity

theorem thetaMono : ThetaMono := by
  intro σ ε ε' x hσ hε hεε hx
  unfold th
  have h1 : 0 < x + ε := by linarith
  have h2 : 0 < x + ε' := by linarith
  refine Real.rpow_le_rpow (div_nonneg hx.le h2.le) ?_ hσ
  exact div_le_div_of_nonneg_left hx.le h1 (by linarith)

theorem thetaBound : ThetaBound := by
  intro hC σ ε hσ hε p x hx
  unfold ld
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => (1 + ε * Real.exp (-u)) ^ (-σ) := by
    funext u; exact thetaForm ε σ hε u
  rw [this]
  have h := hC σ ε hσ hε p (Real.log x)
  rwa [← thetaForm ε σ hε (Real.log x), Real.exp_log hx] at h

theorem iterDeriv_const' (p : ℕ) (k t : ℝ) : iteratedDeriv p (fun _ : ℝ => k) t = if p = 0 then k else 0 := by
  cases p with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ']

theorem cutBound : CutBound := by
  intro c m p hm
  set h : ℝ → ℝ := fun t => c.χ (Real.exp t) ^ m with hh
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := (c.smooth.comp Real.contDiff_exp).pow m
  have hcont : Continuous (iteratedDeriv p h) := hsm.continuous_iteratedDeriv p (by exact_mod_cast le_top)
  have hlow : ∀ t, t < Real.log (1/2) → iteratedDeriv p h t = 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      have : Real.exp s ≤ 1/2 := by
        have := Real.exp_lt_exp.mpr hs
        rw [Real.exp_log (by norm_num)] at this; exact this.le
      simp only [hh, c.zero _ this]
      exact zero_pow (by omega)
    rw [this.iteratedDeriv_eq p, iterDeriv_const']; simp
  have hhigh : ∀ t, 0 < t → iteratedDeriv p h t = if p = 0 then 1 else 0 := by
    intro t ht
    have : h =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      have : 1 ≤ Real.exp s := Real.one_le_exp (le_of_lt hs)
      simp [hh, c.one _ this]
    rw [this.iteratedDeriv_eq p, iterDeriv_const']
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := Real.log (1/2)) (b := 0)).exists_bound_of_continuousOn hcont.continuousOn
  have hbd : ∀ t, |iteratedDeriv p h t| ≤ max C0 1 := by
    intro t
    rcases lt_or_ge t (Real.log (1/2)) with h1 | h1
    · rw [hlow t h1]; simp
    · rcases lt_or_ge 0 t with h2 | h2
      · rw [hhigh t h2]; split_ifs <;> simp
      · exact (hC0 t ⟨h1, h2⟩).trans (le_max_left _ _)
  have key : ∀ ε x : ℝ, 0 < ε → ld p (c.sc ε m) x = iteratedDeriv p h (Real.log x - Real.log ε) := by
    intro ε x hε
    unfold ld
    have : (fun u : ℝ => c.sc ε m (Real.exp u)) = fun u : ℝ => h (u - Real.log ε) := by
      funext u; simp only [hh, Cut.sc]; rw [Real.exp_sub, Real.exp_log hε]
    rw [this, iteratedDeriv_comp_sub_const]
  refine ⟨max C0 1, fun ε x hε hx => ?_⟩
  rw [key ε x hε]
  refine ⟨hbd _, fun hlt => hlow _ ?_, fun hlt => hhigh _ ?_⟩
  · rw [← Real.log_div hx.ne' hε.ne']
    refine Real.log_lt_log (by positivity) ?_
    rw [div_lt_iff₀ hε]; linarith
  · have := Real.log_lt_log hε hlt; linarith

theorem sq_comb_le (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a)
    (D : ℕ → Fn B A') (M : ℕ) (k : ℕ → B.Ω → ℝ) (K : ℝ) (hK : ∀ p ∈ range (M+1), ∀ ω, |k p ω| ≤ K) (ω : B.Ω) :
    LE.sq B wt (fun ω a => ∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial) ω ≤
      (M + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (D p) ω := by
  unfold LE.sq
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.mul_sum]
  have h1 : ‖∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial‖ ≤ ∑ p ∈ range (M+1), K * ‖D p ω a‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    have hf : (1:ℝ) ≤ p.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr p.factorial_ne_zero
    calc |k p ω| * ‖D p ω a‖ / p.factorial ≤ |k p ω| * ‖D p ω a‖ := div_le_self (by positivity) hf
      _ ≤ K * ‖D p ω a‖ := mul_le_mul_of_nonneg_right (hK p hp ω) (norm_nonneg _)
  have h2 : (∑ p ∈ range (M+1), K * ‖D p ω a‖) ^ 2 ≤ (M + 1) * ∑ p ∈ range (M+1), (K * ‖D p ω a‖) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range (M+1)) (f := fun p => K * ‖D p ω a‖)
    simpa using this
  have h3 : ‖∑ p ∈ range (M + 1), (k p ω : ℂ) * D p ω a / p.factorial‖ ^ 2 ≤
      (M + 1) * K ^ 2 * ∑ p ∈ range (M+1), ‖D p ω a‖ ^ 2 := by
    calc _ ≤ (∑ p ∈ range (M+1), K * ‖D p ω a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ = _ := by simp_rw [mul_pow]; rw [← Finset.mul_sum]; ring
  calc wt ω a * _ ≤ wt ω a * ((M + 1) * K ^ 2 * ∑ p ∈ range (M+1), ‖D p ω a‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (hpos ω a)
    _ = _ := by ring

theorem meas_sq (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (v : Fn B A')
    (h1 : ∀ a, Measurable fun ω => wt ω a) (h2 : ∀ a, Measurable fun ω => v ω a) : Measurable (LE.sq B wt v) := by
  unfold LE.sq
  exact Finset.measurable_sum _ fun a _ => (h1 a).mul ((h2 a).norm.pow_const 2)

theorem sq_nonneg' (B : Base) {A' : Type} [Fintype A'] (wt : B.Ω → A' → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (v : Fn B A') (ω) :
    0 ≤ LE.sq B wt v ω := Finset.sum_nonneg fun a _ => mul_nonneg (hpos ω a) (by positivity)

theorem limit_L2 : CutoffLimitInL2 := by
  intro hLeib hCut B A A' _ T u wt c M m hm hpos hmw hJ hP hmS hI
  choose Cf hCf using fun p => hCut c m p hm
  set K : ℝ := (∑ p ∈ range (M+1), |Cf p|) + 1 with hKdef
  have hCK : ∀ p ∈ range (M+1), |Cf p| ≤ K - 1 := by
    intro p hp
    have := Finset.single_le_sum (f := fun p => |Cf p|) (fun i _ => abs_nonneg _) hp
    simp only [hKdef]; linarith
  have hg : Integrable (fun ω => ((M:ℝ) + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (dS B T u p) ω) B.μ :=
    (integrable_finsetSum _ fun p _ => hI p).const_mul _
  have hform : ∀ ε : ℝ, T (mulF B (c.sc ε m) u) =
      fun ω a => ∑ p ∈ range (M + 1), ((ld p (c.sc ε m) (B.G ω) : ℝ) : ℂ) * dS B T u p ω a / p.factorial := by
    intro ε; funext ω a; exact hLeib B A A' T u M hJ hP _ (smoothLog_sc c ε m) ω a
  have hmT : ∀ (ε : ℝ) a, Measurable fun ω => T (mulF B (c.sc ε m) u) ω a := by
    intro ε a
    rw [hform]
    refine Finset.measurable_sum _ fun p _ => ?_
    refine Measurable.div_const (Measurable.mul ?_ (hmS p a)) _
    exact Complex.measurable_ofReal.comp ((meas_ld p _ (smoothLog_sc c ε m)).comp B.G_meas)
  have hmTu : ∀ a, Measurable fun ω => T u ω a := by
    intro a; have := hmS 0 a; rwa [dS_zero] at this
  constructor
  · intro ε hε
    refine hg.mono' (meas_sq B wt _ hmw (hmT ε)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω), hform]
    refine sq_comb_le B wt hpos (dS B T u) M (fun p ω => ld p (c.sc ε m) (B.G ω)) K ?_ ω
    intro p hp ω
    have := (hCf p ε (B.G ω) hε (B.G_pos ω)).1
    have h2 := hCK p hp
    linarith [le_abs_self (Cf p)]
  · have hdiff : ∀ ε : ℝ, (fun ω a => T (mulF B (c.sc ε m) u) ω a - T u ω a) =
        fun ω a => ∑ p ∈ range (M + 1),
          ((ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0) : ℝ) : ℂ) * dS B T u p ω a / p.factorial := by
      intro ε; funext ω a
      rw [hform]
      have : T u ω a = ∑ p ∈ range (M+1), (((if p = 0 then 1 else 0 : ℝ)) : ℂ) * dS B T u p ω a / p.factorial := by
        rw [Finset.sum_eq_single 0]
        · simp [dS_zero]
        · intro p _ hp; simp [hp]
        · intro h; simp at h
      rw [this, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      push_cast; ring
    suffices key : Tendsto (fun ε : ℝ => ∫ ω, LE.sq B wt (fun ω a => T (mulF B (c.sc ε m) u) ω a - T u ω a) ω ∂B.μ)
        (𝓝[>] 0) (𝓝 (∫ _ω, (0:ℝ) ∂B.μ)) by simpa using key
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ω => ((M:ℝ) + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (dS B T u p) ω) ?_ ?_ hg ?_
    · refine Eventually.of_forall fun ε => ?_
      exact (meas_sq B wt _ hmw (fun a => (hmT ε a).sub (hmTu a))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω), hdiff]
      refine sq_comb_le B wt hpos (dS B T u) M
        (fun p ω => ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0)) K ?_ ω
      intro p hp ω
      have h1 := (hCf p ε (B.G ω) hε (B.G_pos ω)).1
      have h2 := hCK p hp
      have h3 : |(if p = 0 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      calc _ ≤ |ld p (c.sc ε m) (B.G ω)| + |(if p = 0 then (1:ℝ) else 0)| := abs_sub _ _
        _ ≤ K := by linarith [le_abs_self (Cf p)]
    · refine Eventually.of_forall fun ω => ?_
      refine tendsto_const_nhds.congr' ?_
      have : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo 0 (B.G ω) := Ioo_mem_nhdsGT (B.G_pos ω)
      filter_upwards [this] with ε hε
      rw [hdiff]
      unfold LE.sq
      symm
      refine Finset.sum_eq_zero fun a _ => ?_
      have : ∑ p ∈ range (M + 1),
          ((ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0) : ℝ) : ℂ) * dS B T u p ω a / p.factorial = 0 := by
        refine Finset.sum_eq_zero fun p _ => ?_
        rw [(hCf p ε (B.G ω) hε.1 (B.G_pos ω)).2.2 hε.2]; simp
      beta_reduce
      rw [this]; simp

theorem amgm (a b δ : ℝ) (hδ : 0 < δ) : a * b ≤ (a ^ 2 / δ + δ * b ^ 2) / 2 := by
  have h := sq_nonneg (a - δ * b)
  have : a ^ 2 / δ + δ * b ^ 2 - 2 * (a * b) = (a - δ * b) ^ 2 / δ := by field_simp; ring
  have h2 : 0 ≤ (a - δ * b) ^ 2 / δ := by positivity
  linarith

theorem pr_bound (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (δ : ℝ) (hδ : 0 < δ) (ω : B.Ω) : ‖pr B wt a b ω‖ ≤ (LE.sq B wt a ω / δ + δ * LE.sq B wt b ω) / 2 := by
  unfold pr LE.sq
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos ω i)]
  have := mul_le_mul_of_nonneg_left (amgm ‖a ω i‖ ‖b ω i‖ δ hδ) (hpos ω i)
  calc _ = wt ω i * (‖a ω i‖ * ‖b ω i‖) := by ring
    _ ≤ _ := this
    _ = _ := by ring

theorem meas_pr (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (a b : Fn B A)
    (h0 : ∀ i, Measurable fun ω => wt ω i) (h1 : ∀ i, Measurable fun ω => a ω i) (h2 : ∀ i, Measurable fun ω => b ω i) :
    Measurable (pr B wt a b) := by
  unfold pr
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((Complex.measurable_ofReal.comp (h0 i)).mul (h1 i)).mul (Complex.continuous_conj.measurable.comp (h2 i))

theorem int_pr (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (h0 : ∀ i, Measurable fun ω => wt ω i) (h1 : ∀ i, Measurable fun ω => a ω i) (h2 : ∀ i, Measurable fun ω => b ω i)
    (ha : Integrable (LE.sq B wt a) B.μ) (hb : Integrable (LE.sq B wt b) B.μ) : Integrable (pr B wt a b) B.μ := by
  refine Integrable.mono' (((ha.div_const 1).add (hb.const_mul 1)).div_const 2)
    (meas_pr B wt a b h0 h1 h2).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  exact pr_bound B wt hpos a b 1 one_pos ω

theorem norm_int_pr_le (B : Base) {A : Type} [Fintype A] (wt : B.Ω → A → ℝ) (hpos : ∀ ω a, 0 ≤ wt ω a) (a b : Fn B A)
    (ha : Integrable (LE.sq B wt a) B.μ) (hb : Integrable (LE.sq B wt b) B.μ) (δ : ℝ) (hδ : 0 < δ) :
    ‖∫ ω, pr B wt a b ω ∂B.μ‖ ≤ ((∫ ω, LE.sq B wt a ω ∂B.μ) / δ + δ * ∫ ω, LE.sq B wt b ω ∂B.μ) / 2 := by
  refine (norm_integral_le_of_norm_le (((ha.div_const δ).add (hb.const_mul δ)).div_const 2)
    (Eventually.of_forall fun ω => pr_bound B wt hpos a b δ hδ ω)).trans (le_of_eq ?_)
  rw [integral_div, integral_add' (ha.div_const δ) (hb.const_mul δ), integral_div, integral_const_mul]

theorem pairLimit : PairLimit := by
  intro B A _ wt v v' f f' hpos hmw hmv hmv' hmf hmf' hIv hIv' hIf hIf' hT hT'
  set V : ℝ := ∫ ω, LE.sq B wt v ω ∂B.μ
  set V' : ℝ := ∫ ω, LE.sq B wt v' ω ∂B.μ
  have hV : 0 ≤ V := integral_nonneg fun ω => sq_nonneg' B wt hpos _ ω
  have hV' : 0 ≤ V' := integral_nonneg fun ω => sq_nonneg' B wt hpos _ ω
  have hIsub : ∀ (g w : Fn B A), (∀ a, Measurable fun ω => g ω a) → (∀ a, Measurable fun ω => w ω a) →
      Integrable (LE.sq B wt g) B.μ → Integrable (LE.sq B wt w) B.μ →
      Integrable (LE.sq B wt (fun ω a => g ω a - w ω a)) B.μ := by
    intro g w hg hw hIg hIw
    refine Integrable.mono' ((hIg.const_mul 2).add (hIw.const_mul 2))
      (meas_sq B wt _ hmw fun a => (hg a).sub (hw a)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω)]
    simp only [LE.sq, Pi.add_apply, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 : ‖g ω a - w ω a‖ ≤ ‖g ω a‖ + ‖w ω a‖ := norm_sub_le _ _
    have h2 : ‖g ω a - w ω a‖ ^ 2 ≤ 2 * ‖g ω a‖ ^ 2 + 2 * ‖w ω a‖ ^ 2 := by
      nlinarith [norm_nonneg (g ω a - w ω a), sq_nonneg (‖g ω a‖ - ‖w ω a‖), norm_nonneg (g ω a), norm_nonneg (w ω a)]
    nlinarith [hpos ω a]
  rw [Metric.tendsto_nhds]
  intro η hη
  set δ : ℝ := η / (V + V' + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hsum : Tendsto (fun ε : ℝ => ((∫ ω, LE.sq B wt (fun ω a => f ε ω a - v ω a) ω ∂B.μ) +
      ∫ ω, LE.sq B wt (fun ω a => f' ε ω a - v' ω a) ω ∂B.μ) * (1 / 2 + 1 / (2 * δ))) (𝓝[>] 0) (𝓝 0) := by
    have := (hT.add hT').mul_const (1 / 2 + 1 / (2 * δ))
    simpa using this
  have hev := (tendsto_order.mp hsum).2 (η / 2) (by positivity)
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hpos'
  have hε0 : 0 < ε := hpos'
  set a1 : Fn B A := fun ω a => f ε ω a - v ω a
  set a2 : Fn B A := fun ω a => f' ε ω a - v' ω a
  have hI1 : Integrable (LE.sq B wt a1) B.μ := hIsub _ _ (fun a => hmf ε a hε0) hmv (hIf ε hε0) hIv
  have hI2 : Integrable (LE.sq B wt a2) B.μ := hIsub _ _ (fun a => hmf' ε a hε0) hmv' (hIf' ε hε0) hIv'
  have hm1 : ∀ a, Measurable fun ω => a1 ω a := fun a => (hmf ε a hε0).sub (hmv a)
  have hm2 : ∀ a, Measurable fun ω => a2 ω a := fun a => (hmf' ε a hε0).sub (hmv' a)
  have hdec : ∀ ω, pr B wt (f ε) (f' ε) ω - pr B wt v v' ω =
      pr B wt a1 a2 ω + pr B wt a1 v' ω + pr B wt v a2 ω := by
    intro ω
    simp only [pr, a1, a2, map_sub]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have i1 := int_pr B wt hpos a1 a2 hmw hm1 hm2 hI1 hI2
  have i2 := int_pr B wt hpos a1 v' hmw hm1 hmv' hI1 hIv'
  have i3 := int_pr B wt hpos v a2 hmw hmv hm2 hIv hI2
  have i4 := int_pr B wt hpos (f ε) (f' ε) hmw (fun a => hmf ε a hε0) (fun a => hmf' ε a hε0) (hIf ε hε0) (hIf' ε hε0)
  have i5 := int_pr B wt hpos v v' hmw hmv hmv' hIv hIv'
  rw [dist_eq_norm, ← integral_sub i4 i5]
  simp_rw [hdec]
  have h12 : Integrable (fun ω => pr B wt a1 a2 ω + pr B wt a1 v' ω) B.μ := i1.add i2
  rw [integral_add h12 i3, integral_add i1 i2]
  have b1 := norm_int_pr_le B wt hpos a1 a2 hI1 hI2 1 one_pos
  have b2 := norm_int_pr_le B wt hpos a1 v' hI1 hIv' δ hδ
  have b3 := norm_int_pr_le B wt hpos v a2 hIv hI2 (1/δ) (by positivity)
  have hδV : δ * (V + V') < η := by
    rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  set E1 : ℝ := ∫ ω, LE.sq B wt a1 ω ∂B.μ
  set E2 : ℝ := ∫ ω, LE.sq B wt a2 ω ∂B.μ
  have e3 : V / (1/δ) = δ * V := by field_simp
  have e4 : (E1 + E2) * (1 / 2 + 1 / (2 * δ)) = (E1 / 1 + 1 * E2) / 2 + E1 / δ / 2 + 1 / δ * E2 / 2 := by
    field_simp; ring
  calc _ ≤ ‖∫ ω, pr B wt a1 a2 ω ∂B.μ‖ + ‖∫ ω, pr B wt a1 v' ω ∂B.μ‖ + ‖∫ ω, pr B wt v a2 ω ∂B.μ‖ :=
        norm_add₃_le
    _ ≤ (E1 / 1 + 1 * E2) / 2 + (E1 / δ + δ * V') / 2 + (V / (1/δ) + 1/δ * E2) / 2 := by
        gcongr
    _ = (E1 + E2) * (1 / 2 + 1 / (2 * δ)) + δ * (V + V') / 2 := by rw [e4, e3]; ring
    _ < η := by linarith

theorem limitB : LimitB := by
  intro hA hL2 hPair hCoef hLeib hCut B N F c hInf hImp hCl Y hY
  obtain ⟨hM, hPos, hFac, hBN, hMon, hJet⟩ := hImp
  obtain ⟨hPoly, hp⟩ := hA hCoef B N F hInf hM hPos hFac hBN hMon hCl Y hY
  have hpos : ∀ ω a, 0 ≤ F.dw Y ω a := fun ω a =>
    mul_nonneg (pow_nonneg (hPos.1 ω).le N) (hPos.2 Y hY a).le
  have hmw : ∀ a, Measurable fun ω => F.dw Y ω a := fun a => (hM.1.pow_const N).mul_const _
  have hmS : ∀ p a, Measurable fun ω => dS B (F.gw Y) F.u p ω a := fun p a => (hp p).1 a
  have L := hL2 hLeib hCut B F.R F.ι (F.gw Y) F.u (F.dw Y) c (N * (F.r + 1)) 1 le_rfl hpos hmw (hJet Y hY) hPoly
    hmS (fun p => (hp p).2)
  have hmg : ∀ a, Measurable fun ω => F.gw Y F.u ω a := by
    intro a; have := hmS 0 a; rwa [dS_zero] at this
  have hmT : ∀ (ε : ℝ) a, Measurable fun ω => F.gw Y (mulF B (c.sc ε 1) F.u) ω a :=
    fun ε a => measurable_apply_mulF_of_jetLocal hLeib B (F.gw Y) F.u _ (hJet Y hY) hPoly hmS _ (smoothLog_sc c ε 1) a
  have P := hPair B F.ι (F.dw Y) (F.gw Y F.u) (F.gw Y F.u) (fun ε => F.gw Y (mulF B (c.sc ε 1) F.u))
    (fun ε => F.gw Y (mulF B (c.sc ε 1) F.u)) hpos hmw hmg hmg (fun ε a _ => hmT ε a) (fun ε a _ => hmT ε a)
    (hCl Y hY) (hCl Y hY) L.1 L.1 L.2 L.2
  simp_rw [int_pr_self] at P
  have := (Complex.continuous_re.tendsto _).comp P
  simpa [Function.comp_def] using this

theorem lemmaEprime : LemmaEprime :=
  lemmaEprimeFromSteps leibniz cutBound limit_L2 pairLimit epStep5 epStep6

theorem ld_zero' (φ : ℝ → ℝ) (x : ℝ) (hx : 0 < x) : ld 0 φ x = φ x := by
  simp [ld, Real.exp_log hx]

theorem fatouStep : FatouStep := by
  intro hRange hLim B A _ wt v σ K hσ hpos hmw hmv hInt hBd
  have hsqm : Measurable (LE.sq B wt v) := meas_sq B wt v hmw hmv
  have hsq0 : ∀ ω, 0 ≤ LE.sq B wt v ω := sq_nonneg' B wt hpos v
  set e : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 1) with he
  have he0 : ∀ n, 0 < e n := fun n => by simp only [he]; positivity
  have hte : Tendsto e atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall he0⟩
  have hmth : ∀ ε : ℝ, Measurable fun ω => th ε σ (B.G ω) := fun ε => by
    unfold th; exact (B.G_meas.div (B.G_meas.add_const ε)).pow_const σ
  have hlim : ∀ ω, Tendsto (fun n => th (e n) σ (B.G ω) * LE.sq B wt v ω) atTop (𝓝 (LE.sq B wt v ω)) := by
    intro ω
    have h := (hLim σ 0 (B.G ω) (B.G_pos ω)).comp hte
    simp only [Function.comp_def, ld_zero' _ _ (B.G_pos ω), if_true] at h
    simpa using h.mul_const (LE.sq B wt v ω)
  have hK0 : 0 ≤ K := by
    refine le_trans (integral_nonneg fun ω => ?_) (hBd 1 one_pos)
    exact mul_nonneg (hRange 1 σ _ one_pos hσ (B.G_pos ω)).1.le (hsq0 ω)
  have hle : ∫⁻ ω, ENNReal.ofReal (LE.sq B wt v ω) ∂B.μ ≤ ENNReal.ofReal K := by
    calc ∫⁻ ω, ENNReal.ofReal (LE.sq B wt v ω) ∂B.μ
        = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (th (e n) σ (B.G ω) * LE.sq B wt v ω)) atTop ∂B.μ := by
          refine lintegral_congr fun ω => ?_
          exact ((ENNReal.tendsto_ofReal (hlim ω)).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (th (e n) σ (B.G ω) * LE.sq B wt v ω) ∂B.μ) atTop :=
          lintegral_liminf_le fun n => ((hmth (e n)).mul hsqm).ennreal_ofReal
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal K) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hInt (e n) (he0 n))
            (Eventually.of_forall fun ω => mul_nonneg (hRange (e n) σ _ (he0 n) hσ (B.G_pos ω)).1.le (hsq0 ω))]
          exact ENNReal.ofReal_le_ofReal (hBd (e n) (he0 n))
      _ = ENNReal.ofReal K := by simp
  refine ⟨⟨hsqm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hsq0)]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hsq0) hsqm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hK0 hle

noncomputable def Fk (k : ℕ) (s : ℝ) (t : ℝ) : ℝ := Real.exp (-(k:ℝ) * t) * (1 + Real.exp (-t)) ^ (-s)

theorem Fk_contDiff (k : ℕ) (s : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fk k s) := by
  unfold Fk
  refine (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul ?_
  refine ContDiff.rpow_const_of_ne ?_ ?_
  · exact contDiff_const.add (Real.contDiff_exp.comp contDiff_neg)
  · intro u; positivity

theorem Fk_deriv (k : ℕ) (s : ℝ) : deriv (Fk k s) = fun t => -(k:ℝ) * Fk k s t + s * Fk (k+1) (s+1) t := by
  funext t
  have hp : 0 < 1 + Real.exp (-t) := by positivity
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(k:ℝ) * t)) (Real.exp (-(k:ℝ) * t) * (-(k:ℝ) * 1)) t :=
    ((hasDerivAt_id t).const_mul (-(k:ℝ))).exp
  have h2 : HasDerivAt (fun t : ℝ => 1 + Real.exp (-t)) (Real.exp (-t) * (-1)) t :=
    ((hasDerivAt_id t).neg.exp).const_add 1
  have h3 := h2.rpow_const (p := -s) (Or.inl hp.ne')
  have h4 := h1.mul h3
  have h5 : deriv (Fk k s) t = _ := h4.deriv
  rw [h5]
  unfold Fk
  have e1 : Real.exp (-((k+1 : ℕ):ℝ) * t) = Real.exp (-(k:ℝ) * t) * Real.exp (-t) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  have e2 : -s - 1 = -(s+1) := by ring
  rw [e1, e2]; ring

theorem Fk_lim (k : ℕ) (s : ℝ) : Tendsto (Fk k s) atTop (𝓝 (if k = 0 then 1 else 0)) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h1 : Tendsto (fun t : ℝ => (1 + Real.exp (-t)) ^ (-s)) atTop (𝓝 1) := by
    have := (h0.const_add 1).rpow_const (p := -s) (Or.inl (by norm_num))
    simpa using this
  unfold Fk
  split_ifs with hk
  · subst hk; simpa using h1
  · have h2 : Tendsto (fun t : ℝ => Real.exp (-(k:ℝ) * t)) atTop (𝓝 0) := by
      have hk' : (0:ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      have : Tendsto (fun t : ℝ => (k:ℝ) * t) atTop atTop := tendsto_id.const_mul_atTop hk'
      have := h0.comp this
      simpa [Function.comp_def] using this
    simpa using h2.mul h1

theorem Fk_iter_lim (p : ℕ) : ∀ (k : ℕ) (s : ℝ),
    Tendsto (iteratedDeriv p (Fk k s)) atTop (𝓝 (if p = 0 ∧ k = 0 then 1 else 0)) := by
  induction p with
  | zero => intro k s; simpa using Fk_lim k s
  | succ n ih =>
    intro k s
    rw [iteratedDeriv_succ', Fk_deriv]
    have hadd : iteratedDeriv n (fun t => -(k:ℝ) * Fk k s t + s * Fk (k+1) (s+1) t) =
        fun t => -(k:ℝ) * iteratedDeriv n (Fk k s) t + s * iteratedDeriv n (Fk (k+1) (s+1)) t := by
      funext t
      have c1 : ContDiffAt ℝ n (fun t => -(k:ℝ) * Fk k s t) t :=
        (contDiff_const.mul ((Fk_contDiff k s).of_le (by exact_mod_cast le_top))).contDiffAt
      have c2 : ContDiffAt ℝ n (fun t => s * Fk (k+1) (s+1) t) t :=
        (contDiff_const.mul ((Fk_contDiff (k+1) (s+1)).of_le (by exact_mod_cast le_top))).contDiffAt
      rw [iteratedDeriv_fun_add c1 c2, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
    rw [hadd]
    have t1 := (ih k s).const_mul (-(k:ℝ))
    have t2 := (ih (k+1) (s+1)).const_mul s
    have := t1.add t2
    have hval : -(k:ℝ) * (if n = 0 ∧ k = 0 then 1 else 0) + s * (if n = 0 ∧ k + 1 = 0 then 1 else 0) =
        (if n + 1 = 0 ∧ k = 0 then (1:ℝ) else 0) := by
      by_cases hk : k = 0 <;> simp [hk]
    rw [hval] at this
    exact this

theorem thetaLimit : ThetaLimit := by
  intro σ p x hx
  have hlog : Tendsto (fun ε : ℝ => Real.log x - Real.log ε) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_nhdsGT_zero
    have h2 : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] 0) atTop := tendsto_neg_atBot_atTop.comp this
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_left _ (Real.log x) h2
  have h := (Fk_iter_lim p 0 σ).comp hlog
  simp only [and_true] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  unfold ld
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => Fk 0 σ (u - Real.log ε) := by
    funext u
    rw [thetaForm ε σ hε0 u]
    unfold Fk
    have : Real.exp (-(u - Real.log ε)) = ε * Real.exp (-u) := by
      rw [neg_sub, Real.exp_sub, Real.exp_log hε0, Real.exp_neg]; ring
    rw [this]; simp
  rw [this, iteratedDeriv_comp_sub_const]
  rfl

end Formalism.FourierDecayAlt.P.LEx2
