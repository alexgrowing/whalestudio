import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightLeOfMemWtSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotCdomAdd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivedModuleCoefficientsAndStableFlows

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.Anal

private theorem hasDerivAt_taylor_remainder {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] (f : ℕ → ℝ → H)
    (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (s : ℝ) (N : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => f 0 (s + w) - ∑ k ∈ range (N + 1 + 1), (w ^ k / (k.factorial : ℝ)) • f k s)
      (f 1 (s + z) - ∑ k ∈ range (N + 1), (z ^ k / (k.factorial : ℝ)) • f (k + 1) s) z := by
  have e : ∀ w : ℝ, ∑ k ∈ range (N + 1 + 1), (w ^ k / (k.factorial : ℝ)) • f k s =
      ∑ k ∈ range (N + 1), (w ^ (k + 1) / ((k + 1).factorial : ℝ)) • f (k + 1) s + f 0 s := by
    intro w
    rw [Finset.sum_range_succ']
    simp
  have h1 : HasDerivAt (fun w : ℝ => f 0 (s + w)) (f 1 (s + z)) z := (hd 0 (s + z)).comp_const_add s z
  have h2 : HasDerivAt (fun w : ℝ => ∑ k ∈ range (N + 1), (w ^ (k + 1) / ((k + 1).factorial : ℝ)) • f (k + 1) s)
      (∑ k ∈ range (N + 1), (z ^ k / (k.factorial : ℝ)) • f (k + 1) s) z := by
    apply HasDerivAt.fun_sum
    intro k _
    have hp := ((hasDerivAt_pow (k + 1) z).div_const ((k + 1).factorial : ℝ)).smul_const (f (k + 1) s)
    convert hp using 2
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    have : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have h3 := h1.sub (h2.add_const (f 0 s))
  convert h3 using 1
  funext w
  rw [e w]
  rfl

private theorem norm_taylor_remainder_le {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] (N : ℕ) :
    ∀ (f : ℕ → ℝ → H) (M : ℕ → ℝ), (∀ k t, HasDerivAt (f k) (f (k + 1) t) t) → (∀ k t, ‖f k t‖ ≤ M k) →
      ∀ s z : ℝ, ‖f 0 (s + z) - ∑ k ∈ range (N + 1), (z ^ k / (k.factorial : ℝ)) • f k s‖ ≤
        |z| ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1) := by
  induction N with
  | zero =>
    intro f M hd hM s z
    have hφ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => f 0 (s + τ * z)) (z • f 1 (s + τ * z)) τ := by
      intro τ
      have h2 : HasDerivAt (fun τ : ℝ => s + τ * z) z τ := by
        simpa using ((hasDerivAt_id τ).mul_const z).const_add s
      exact (hd 0 (s + τ * z)).scomp τ h2
    have key := norm_image_sub_le_of_norm_deriv_right_le_segment (a := 0) (b := 1)
      (f := fun τ : ℝ => f 0 (s + τ * z)) (C := |z| * M 1)
      (fun τ _ => (hφ τ).continuousAt.continuousWithinAt) (fun τ _ => (hφ τ).hasDerivWithinAt)
      (fun τ _ => by rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hM 1 _) (abs_nonneg z))
      1 ⟨zero_le_one, le_rfl⟩
    simpa [mul_comm] using key
  | succ N ih =>
    intro f M hd hM s z
    have hφ : ∀ τ : ℝ, HasDerivAt
        (fun τ : ℝ => f 0 (s + τ * z) - ∑ k ∈ range (N + 1 + 1), ((τ * z) ^ k / (k.factorial : ℝ)) • f k s)
        (z • (f 1 (s + τ * z) - ∑ k ∈ range (N + 1), ((τ * z) ^ k / (k.factorial : ℝ)) • f (k + 1) s)) τ := by
      intro τ
      have h2 : HasDerivAt (fun τ : ℝ => τ * z) z τ := by simpa using (hasDerivAt_id τ).mul_const z
      exact (hasDerivAt_taylor_remainder f hd s N (τ * z)).scomp τ h2
    have hB : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => |z| ^ (N + 1 + 1) * τ ^ (N + 1 + 1) / ((N + 1 + 1).factorial : ℝ) * M (N + 1 + 1))
        (|z| ^ (N + 1 + 1) * τ ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1 + 1)) τ := by
      intro τ
      have hp := (((hasDerivAt_pow (N + 1 + 1) τ).const_mul (|z| ^ (N + 1 + 1))).div_const
        ((N + 1 + 1).factorial : ℝ)).mul_const (M (N + 1 + 1))
      refine hp.congr_deriv ?_
      rw [Nat.add_sub_cancel, Nat.factorial_succ (N + 1)]
      push_cast
      have : ((N + 1).factorial : ℝ) ≠ 0 := by positivity
      field_simp
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1)
      (fun τ _ => (hφ τ).continuousAt.continuousWithinAt) (fun τ _ => (hφ τ).hasDerivWithinAt)
      (by simp [Finset.sum_range_succ']) hB
      (fun τ hτ => by
        rw [norm_smul, Real.norm_eq_abs]
        have h := ih (fun k => f (k + 1)) (fun k => M (k + 1)) (fun k t => hd (k + 1) t) (fun k t => hM (k + 1) t)
          s (τ * z)
        calc |z| * ‖f 1 (s + τ * z) - ∑ k ∈ range (N + 1), ((τ * z) ^ k / (k.factorial : ℝ)) • f (k + 1) s‖
            ≤ |z| * (|τ * z| ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1 + 1)) :=
              mul_le_mul_of_nonneg_left h (abs_nonneg z)
          _ = |z| ^ (N + 1 + 1) * τ ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1 + 1) := by
              rw [abs_mul, abs_of_nonneg hτ.1]
              ring)
      (x := 1) ⟨zero_le_one, le_rfl⟩
    simpa using key

theorem analytic_chain {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] (f : ℕ → ℝ → H)
    (M : ℕ → ℝ) (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (hM : ∀ k t, ‖f k t‖ ≤ M k) (r : ℝ) (hr : 0 < r)
    (hs : Summable fun k : ℕ => r ^ k * M k / (k.factorial : ℝ)) : AnalyticOnNhd ℝ (f 0) Set.univ := by
  have hM0 : ∀ k, 0 ≤ M k := fun k => (norm_nonneg _).trans (hM k 0)
  have hg0 : ∀ k, 0 ≤ r ^ k * M k / (k.factorial : ℝ) := fun k => by
    have := hM0 k
    positivity
  intro s _
  let p : FormalMultilinearSeries ℝ ℝ H := fun k =>
    ContinuousMultilinearMap.mkPiRing ℝ (Fin k) ((1 / (k.factorial : ℝ)) • f k s)
  have hp : ∀ (k : ℕ) (y : ℝ), (p k fun _ => y) = (y ^ k / (k.factorial : ℝ)) • f k s := by
    intro k y
    simp only [p, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_smul]
    congr 1
    ring
  have hpn : ∀ k, ‖p k‖ ≤ M k / (k.factorial : ℝ) := by
    intro k
    simp only [p, ContinuousMultilinearMap.norm_mkPiRing, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (k.factorial : ℝ)), one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (hM k s) (by positivity)
  let ρ : NNReal := ⟨r, hr.le⟩
  have hrad : (ρ : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_bound (∑' k, r ^ k * M k / (k.factorial : ℝ)) fun k => ?_
    calc ‖p k‖ * (ρ : ℝ) ^ k ≤ M k / (k.factorial : ℝ) * r ^ k :=
          mul_le_mul_of_nonneg_right (hpn k) (by positivity)
      _ = r ^ k * M k / (k.factorial : ℝ) := by ring
      _ ≤ _ := hs.le_tsum k fun j _ => hg0 j
  refine ⟨p, ρ, hrad, ENNReal.coe_pos.mpr (NNReal.coe_pos.mp hr), ?_⟩
  intro y hy
  have hy' : |y| ≤ r := by
    rw [Metric.mem_eball, edist_lt_coe, ← NNReal.coe_lt_coe, coe_nndist, Real.dist_eq, sub_zero] at hy
    exact hy.le
  have hsum : Summable fun k : ℕ => (y ^ k / (k.factorial : ℝ)) • f k s := by
    refine hs.of_norm_bounded fun k => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    calc |y| ^ k / (k.factorial : ℝ) * ‖f k s‖ ≤ r ^ k / (k.factorial : ℝ) * M k := by
          gcongr
          all_goals first | exact hM k s | exact hM0 k | exact hy'
      _ = r ^ k * M k / (k.factorial : ℝ) := by ring
  have hlim : Filter.Tendsto (fun N : ℕ => ∑ k ∈ range (N + 1), (y ^ k / (k.factorial : ℝ)) • f k s)
      Filter.atTop (nhds (f 0 (s + y))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
      ((hs.tendsto_atTop_zero).comp (Filter.tendsto_add_atTop_nat 1))
    rw [norm_sub_rev]
    calc _ ≤ |y| ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1) := norm_taylor_remainder_le N f M hd hM s y
      _ ≤ r ^ (N + 1) / ((N + 1).factorial : ℝ) * M (N + 1) := by
          gcongr
          all_goals first | exact hM0 (N + 1) | exact hy'
      _ = r ^ (N + 1) * M (N + 1) / ((N + 1).factorial : ℝ) := by ring
  have hlim2 := (hsum.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have heq := tendsto_nhds_unique hlim2 hlim
  have hfun : (fun k : ℕ => p k fun _ => y) = fun k => (y ^ k / (k.factorial : ℝ)) • f k s :=
    funext fun k => hp k y
  rw [hfun, ← heq]
  exact hsum.hasSum

theorem cas_real {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E) {u : V} (hu : u ≠ 0) {c : ℂ}
    (h : Cas E u = c • u) : c = (c.re : ℂ) := by
  have hsa : ⟪Cas E u, u⟫_ℂ = ⟪u, Cas E u⟫_ℂ := by
    simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hU a b, hU b a, ← mul_assoc]
    have hs : (Formalism.REAL.sgn ε a b : ℂ) * (Formalism.REAL.sgn ε b a : ℂ) = 1 := by
      unfold Formalism.REAL.sgn
      by_cases hab : ε a = ε b
      · simp [hab]
      · simp [hab, Ne.symm hab]
    rw [hs, one_mul]
  rw [h, inner_smul_left, inner_smul_right] at hsa
  have hne : ⟪u, u⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hu
  have hc : (starRingEnd ℂ) c = c := mul_right_cancel₀ hne hsa
  exact (Complex.conj_eq_iff_re.mp hc).symm

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ V}

theorem cas_eigen (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) {μ : Fin n → ℝ} {u : V} (hu0 : u ≠ 0)
    (hu : KHighest ε E μ u) (hf : FiniteDimensional ℂ (kSpan ε E u))
    (hall : ∀ S, IsKTypeOf ε σ μ S → S ≤ (kSpan ε E u).map V.subtype) : ∃ c : ℝ, Cas E u = (c : ℂ) • u := by
  obtain ⟨hGl, hU, -, -⟩ := id hD
  have hcomm := (Formalism.REAL.casCentral (Module.End ℂ V) n ε E hGl).1
  have hKR : KRel ε E := glRel_kRel ε E hGl
  have hKU : KUnit ε E := isUnitary_kUnit ε E hU
  have hyc : ∀ a b w, E a b (Cas E w) = Cas E (E a b w) := fun a b w => by
    rw [← Module.End.mul_apply, ← hcomm a b, Module.End.mul_apply]
  have hyK : KHighest ε E μ (Cas E u) := by
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [hyc, hu.1 a, map_smul]
    · rw [hyc, hu.2 a b hab he, map_zero]
  by_cases hy0 : Cas E u = 0
  · exact ⟨0, by rw [hy0]; simp⟩
  · have hle : kSpan ε E (Cas E u) ≤ (kSpan ε E u).map (Cas E) := by
      refine compactSpan_le_of_mem ε E ⟨u, mem_compactSpan_self ε E u, rfl⟩ ?_
      intro a b hab z hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨E a b w, compactSpan_isCompactInvariant ε E u a b hab w hw, (hyc a b w).symm⟩
    have hfy : FiniteDimensional ℂ (kSpan ε E (Cas E u)) := by
      haveI := hf
      exact Submodule.finiteDimensional_of_le hle
    have hT := (GlobalTheory.Jet.KType.kType_iff n ε H σ V E hσ hD).1 μ (Cas E u) hy0 hyK hfy
    have hymem : Cas E u ∈ kSpan ε E u := by
      obtain ⟨w, hw, hwy⟩ := hall _ hT ⟨Cas E u, mem_compactSpan_self ε E (Cas E u), rfl⟩
      exact (Subtype.ext hwy : w = Cas E u) ▸ hw
    rcases Formalism.REAL.kHiUniq V n ε E μ μ u (Cas E u) hKR hKU hu hymem hyK with h0 | ⟨-, c', hc'⟩
    · exact absurd h0 hy0
    · refine ⟨c'.re, ?_⟩
      have hre := cas_real hU hu0 hc'
      rw [hc', ← hre]

omit [CompleteSpace H] in

theorem pow_growth (hD : IsDer ε σ V E) {μ : Fin n → ℝ} {u : V} (hu : KHighest ε E μ u)
    (hf : FiniteDimensional ℂ (kSpan ε E u)) {c : ℝ} (hc : Cas E u = (c : ℂ) • u) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ w ∈ kSpan ε E u, ∀ k : ℕ,
      ‖(Coef.act E X ^ k) w‖ ≤ C ^ k * (B + k) ^ k * ‖w‖ := by
  obtain ⟨hGl, hU, -, -⟩ := hD
  have hpf := Formalism.REAL.pfilFacts V n ε E u hGl
  have hug := GlobalTheory.FilGrowth.uGrowth V n ε E μ c u hGl hU hu hc hf
  set S : ℝ := ∑ a, ∑ b, ‖X a b‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _
  set s0 : ℝ := Real.sqrt (ckv ε μ) with hs0
  set q : ℝ := Real.sqrt (2 * (n : ℝ)) with hq
  set r0 : ℝ := Real.sqrt |c| with hr0
  have hs0' : 0 ≤ s0 := Real.sqrt_nonneg _
  have hq' : 0 ≤ q := Real.sqrt_nonneg _
  have hr0' : 0 ≤ r0 := Real.sqrt_nonneg _
  have hqq : q ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
  have hrr : r0 ^ 2 = |c| := Real.sq_sqrt (abs_nonneg c)
  have hstep : ∀ (j : ℕ), ∀ x ∈ pfil ε E u j, Coef.act E X x ∈ pfil ε E u (j + 1) ∧
      ‖Coef.act E X x‖ ≤ S * (q + 1) * (s0 + n + r0 + j) * ‖x‖ := by
    intro j x hx
    constructor
    · rw [Coef.act_apply]
      exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
        Submodule.smul_mem _ _ (hpf.2.2.2.1 j a b x hx)
    · have hD2 := hug j x hx
      have hT : 0 ≤ s0 + j + n := by positivity
      have k1 : q * (s0 + j + n) + r0 ≤ (q + 1) * (s0 + n + r0 + j) := by nlinarith
      have k2 : 2 * (n : ℝ) * (s0 + j + n) ^ 2 + |c| ≤ ((q + 1) * (s0 + n + r0 + j)) ^ 2 := by
        rw [← hqq, ← hrr]
        have h0 : 0 ≤ q * (s0 + j + n) + r0 := by positivity
        nlinarith [mul_self_le_mul_self h0 k1, mul_nonneg (mul_nonneg hq' hT) hr0']
      have hsq : ∀ a b, ‖E a b x‖ ≤ (q + 1) * (s0 + n + r0 + j) * ‖x‖ := by
        intro a b
        have h1 : ‖E a b x‖ ^ 2 ≤ ∑ a, ∑ b, ‖E a b x‖ ^ 2 := by
          have ha := Finset.single_le_sum (f := fun a' => ∑ b, ‖E a' b x‖ ^ 2)
            (fun i _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)
          have hb := Finset.single_le_sum (f := fun b' => ‖E a b' x‖ ^ 2) (fun i _ => sq_nonneg _)
            (Finset.mem_univ b)
          exact hb.trans ha
        have h2 : (2 * (n : ℝ) * (s0 + j + n) ^ 2 + |c|) * ‖x‖ ^ 2 ≤
            ((q + 1) * (s0 + n + r0 + j) * ‖x‖) ^ 2 := by
          calc _ ≤ ((q + 1) * (s0 + n + r0 + j)) ^ 2 * ‖x‖ ^ 2 :=
                mul_le_mul_of_nonneg_right k2 (sq_nonneg _)
            _ = _ := by ring
        calc ‖E a b x‖ = Real.sqrt (‖E a b x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (((q + 1) * (s0 + n + r0 + j) * ‖x‖) ^ 2) := Real.sqrt_le_sqrt (h1.trans (hD2.trans h2))
          _ = (q + 1) * (s0 + n + r0 + j) * ‖x‖ := Real.sqrt_sq (by positivity)
      rw [Coef.act_apply]
      calc ‖∑ a, ∑ b, X a b • E a b x‖ ≤ ∑ a, ∑ b, ‖X a b • E a b x‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
        _ ≤ ∑ a, ∑ b, ‖X a b‖ * ((q + 1) * (s0 + n + r0 + j) * ‖x‖) :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by
              rw [norm_smul]
              exact mul_le_mul_of_nonneg_left (hsq a b) (norm_nonneg _)
        _ = S * (q + 1) * (s0 + n + r0 + j) * ‖x‖ := by
          rw [hS]
          simp only [← Finset.sum_mul]
          ring
  refine ⟨s0 + n + r0, S * (q + 1), by positivity, by positivity, ?_⟩
  intro w hw k
  have hw0 : w ∈ pfil ε E u 0 := by
    rw [hpf.1]
    exact hw
  have hg := Formalism.REAL.growthIter V (Coef.act E X) (pfil ε E u) (s0 + n + r0) (S * (q + 1)) (by positivity)
    (by positivity) hstep 0 k w hw0
  simpa only [Nat.cast_zero, add_zero] using hg

theorem lowK_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → IsDer ε σ V E → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → lowKSub ε lam σ ≤ V → ∀ x ∈ lowKSub ε lam σ, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → AnalyticOnNhd ℝ (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) x) Set.univ := by
  intro n ε H _ _ _ σ V E lam hσ hD hK hle x hx X hX
  obtain ⟨-, -, -, ⟨v0, hv0S, hv0, hv0w⟩, -⟩ := id hK
  have hv0V : v0 ∈ V := hle hv0S
  have hu0 : (⟨v0, hv0V⟩ : V) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨huK, hspan, hfin⟩ := (GlobalTheory.Jet.KType.kType_iff n ε H σ V E hσ hD).2 (lowK ε lam) (lowKSub ε lam σ)
    ⟨v0, hv0V⟩ hK hle hv0S hu0 hv0w
  obtain ⟨c, hc⟩ := cas_eigen hσ hD hu0 huK hfin (fun S' h => by rw [hspan]; exact le_sSup h)
  obtain ⟨B, C, hB, hC, hgrow⟩ := pow_growth hD huK hfin hc X
  have hxV : x ∈ V := hle hx
  have hvmem : (⟨x, hxV⟩ : V) ∈ kSpan ε E ⟨v0, hv0V⟩ := by
    rw [← hspan] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    exact (Subtype.ext hwx : w = ⟨x, hxV⟩) ▸ hw
  have hd : ∀ (k : ℕ) (t : ℝ),
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (((Coef.act E X ^ k) ⟨x, hxV⟩ : V) : H))
        (σ (NormedSpace.exp ((t : ℂ) • X)) (((Coef.act E X ^ (k + 1)) ⟨x, hxV⟩ : V) : H)) t := by
    intro k t
    rw [pow_succ', Module.End.mul_apply]
    exact Coef.der_flow hσ hD hX _ t
  have hM : ∀ (k : ℕ) (t : ℝ), ‖σ (NormedSpace.exp ((t : ℂ) • X)) (((Coef.act E X ^ k) ⟨x, hxV⟩ : V) : H)‖ ≤
      C ^ k * (B + k) ^ k * ‖(⟨x, hxV⟩ : V)‖ := by
    intro k t
    have hexp : NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := Formalism.REAL.expUJ n ε X hX t
    rw [hσ.2.1 _ hexp]
    exact hgrow _ hvmem k
  have hr : 0 < 1 / (C * Real.exp 1 + 1) := by positivity
  have hCr : C * (1 / (C * Real.exp 1 + 1)) * Real.exp 1 < 1 := by
    have hpos : 0 < C * Real.exp 1 + 1 := by positivity
    rw [show C * (1 / (C * Real.exp 1 + 1)) * Real.exp 1 = C * Real.exp 1 / (C * Real.exp 1 + 1) by ring,
      div_lt_one hpos]
    linarith
  have hsum := (Formalism.REAL.taylorRadius C B (1 / (C * Real.exp 1 + 1)) hC hB hr.le hCr).mul_right ‖(⟨x, hxV⟩ : V)‖
  have hs : Summable fun k : ℕ => (1 / (C * Real.exp 1 + 1)) ^ k * (C ^ k * (B + k) ^ k * ‖(⟨x, hxV⟩ : V)‖) /
      (k.factorial : ℝ) := by
    refine hsum.congr fun k => ?_
    rw [mul_pow]
    ring
  have h := analytic_chain (fun k t => σ (NormedSpace.exp ((t : ℂ) • X)) (((Coef.act E X ^ k) ⟨x, hxV⟩ : V) : H))
    (fun k => C ^ k * (B + k) ^ k * ‖(⟨x, hxV⟩ : V)‖) hd hM _ hr hs
  simpa using h

end GlobalTheory.Jet.Anal
