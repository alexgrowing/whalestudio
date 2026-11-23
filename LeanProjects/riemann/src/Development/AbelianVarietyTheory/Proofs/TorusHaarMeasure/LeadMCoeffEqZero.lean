import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeadIndep

open Filter

theorem mem_multiLt {D a : ℕ} {α : Fin D → ℕ} : α ∈ multiLt D a ↔ ∑ k, α k < a := by
  simp only [multiLt, Finset.mem_biUnion, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact he
  · intro h
    exact ⟨_, h, rfl⟩

private theorem sum_mul_pow_mul_prod_eq_div_pow {n δ : ℕ} (α : Fin n → ℕ) (c : Fin δ → ℂ) (Φv : Fin δ → ℂ)
    (σv : Fin n → ℂ) (w t : ℂ) (T d : ℕ) (ht : t ≠ 0) (hw : w ≠ 0)
    (hle : (∃ k, c k ≠ 0) → d ≤ ∑ q, α q) :
    (∑ k, c k * Φv k) * t ^ (∑ q, α q - d) * w ^ (∑ q, α q + (T - ∑ q, α q)) *
        ∏ q, (t⁻¹ * (σv q / w)) ^ α q =
      (∑ k, c k * (∏ q, σv q ^ α q) * w ^ (T - ∑ q, α q) * Φv k) / t ^ d := by
  by_cases hz : ∀ k, c k = 0
  · simp [hz]
  push Not at hz
  have hd := hle hz
  have hprod : ∏ q, (t⁻¹ * (σv q / w)) ^ α q = (t⁻¹ * w⁻¹) ^ (∑ q, α q) * ∏ q, σv q ^ α q := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [← mul_pow, div_eq_mul_inv]
    ring
  have hsum : ∑ k, c k * (∏ q, σv q ^ α q) * w ^ (T - ∑ q, α q) * Φv k =
      (∑ k, c k * Φv k) * (∏ q, σv q ^ α q) * w ^ (T - ∑ q, α q) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hprod, hsum]
  generalize ∑ q, α q = s at hd ⊢
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  rw [Nat.add_sub_cancel_left, eq_div_iff (pow_ne_zero d ht)]
  have key : (t⁻¹ * w⁻¹) ^ (d + e) * (t * w) ^ (d + e) = 1 := by
    rw [← mul_pow, show t⁻¹ * w⁻¹ * (t * w) = 1 by field_simp, one_pow]
  linear_combination ((∑ k, c k * Φv k) * (∏ q, σv q ^ α q) * w ^ (T - (d + e))) * key

theorem lowest_degree {n δ : ℕ} (U : Set (V n)) (hU : IsOpen U)
    (vP : V n) (hvP : vP ∈ U) (σ : Fin n → V n → ℂ) (wz : V n → ℂ) (Φ : Fin δ → V n → ℂ)
    (M : Finset (Fin n → ℕ)) (T m d : ℕ) (c : (Fin n → ℕ) → Fin δ → ℂ)
    (hσ : ∀ k, DifferentiableOn ℂ (σ k) U) (hw : DifferentiableOn ℂ wz U)
    (hΦ : ∀ k, DifferentiableOn ℂ (Φ k) U)
    (hσ0 : ∀ k, σ k vP = 0) (hw0 : wz vP ≠ 0)
    (hlow : ∀ α ∈ M, ∀ k, c α k ≠ 0 → d ≤ ∑ q, α q) (hdm : d < m)
    (hb : ∃ C : ℝ, ∀ᶠ v in 𝓝 vP, ‖∑ α ∈ M, ∑ k,
      c α k * (∏ q, σ q v ^ α q) * wz v ^ (T - ∑ q, α q) * Φ k v‖ ≤ C * ‖v - vP‖ ^ m)
    (h0 : V n) :
    ∑ α ∈ M, ((∑ k, c α k * Φ k vP) * 0 ^ (∑ q, α q - d) *
        wz vP ^ (∑ q, α q + (T - ∑ q, α q))) *
      ∏ q, (fderiv ℂ (fun v => WithLp.toLp 2 (fun k => σ k v / wz v)) vP h0) q ^ α q = 0 := by
  classical
  have hUn : U ∈ 𝓝 vP := hU.mem_nhds hvP
  have hwd : DifferentiableAt ℂ wz vP := hw.differentiableAt hUn
  have hΦc : ∀ k, ContinuousAt (Φ k) vP := fun k => ((hΦ k).differentiableAt hUn).continuousAt
  have hFd : DifferentiableAt ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP := by
    have h1 : DifferentiableAt ℂ (fun v => fun k => σ k v / wz v) vP :=
      differentiableAt_pi.2 fun k => by
        simpa only [div_eq_mul_inv, Function.comp_def, Pi.mul_def] using
          ((hσ k).differentiableAt hUn).mul ((differentiableAt_inv hw0).comp vP hwd)
    exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.differentiableAt.comp vP h1
  have hl : HasDerivAt (fun t : ℂ => vP + t • h0) h0 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const h0).const_add vP
  have hl0 : Tendsto (fun t : ℂ => vP + t • h0) (𝓝 0) (𝓝 vP) := by
    simpa using hl.continuousAt.tendsto
  have hl1 : Tendsto (fun t : ℂ => vP + t • h0) (𝓝[≠] 0) (𝓝 vP) := hl0.mono_left nhdsWithin_le_nhds
  have hFl : HasDerivAt (fun t : ℂ => (WithLp.toLp 2
      (fun k => σ k (vP + t • h0) / wz (vP + t • h0)) : V n))
      (fderiv ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP h0) 0 := by
    have hF' : HasFDerivAt (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n))
        (fderiv ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP) (vP + (0 : ℂ) • h0) := by
      rw [zero_smul, add_zero]
      exact hFd.hasFDerivAt
    exact hF'.comp_hasDerivAt 0 hl
  have hcomp : ∀ q, Tendsto (fun t : ℂ => t⁻¹ * (σ q (vP + t • h0) / wz (vP + t • h0))) (𝓝[≠] 0)
      (𝓝 ((fderiv ℂ (fun v => (WithLp.toLp 2 (fun k => σ k v / wz v) : V n)) vP h0) q)) := by
    intro q
    have h2 := ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) q).tendsto _).comp
      (hasDerivAt_iff_tendsto_slope.1 hFl)
    refine h2.congr' (Filter.Eventually.of_forall fun t => ?_)
    simp [slope_def_module, hσ0]
  have hlim : Tendsto (fun t : ℂ => ∑ α ∈ M, ((∑ k, c α k * Φ k (vP + t • h0)) * t ^ (∑ q, α q - d) *
        wz (vP + t • h0) ^ (∑ q, α q + (T - ∑ q, α q))) *
        ∏ q, (t⁻¹ * (σ q (vP + t • h0) / wz (vP + t • h0))) ^ α q) (𝓝[≠] 0)
      (𝓝 (∑ α ∈ M, ((∑ k, c α k * Φ k vP) * 0 ^ (∑ q, α q - d) *
        wz vP ^ (∑ q, α q + (T - ∑ q, α q))) *
        ∏ q, (fderiv ℂ (fun v => WithLp.toLp 2 (fun k => σ k v / wz v)) vP h0) q ^ α q)) := by
    refine tendsto_finsetSum _ fun α _ => ?_
    refine Tendsto.mul (Tendsto.mul (Tendsto.mul ?_ ?_) ?_) ?_
    · exact tendsto_finsetSum _ fun k _ => ((hΦc k).tendsto.comp hl1).const_mul _
    · exact ((continuous_pow _).tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
    · exact (hwd.continuousAt.tendsto.comp hl1).pow _
    · exact tendsto_finsetProd _ fun q _ => (hcomp q).pow _
  have hwne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), wz (vP + t • h0) ≠ 0 :=
    (hwd.continuousAt.tendsto.comp hl1).eventually_ne hw0
  have heq : (fun t : ℂ => (∑ α ∈ M, ∑ k, c α k * (∏ q, σ q (vP + t • h0) ^ α q) *
        wz (vP + t • h0) ^ (T - ∑ q, α q) * Φ k (vP + t • h0)) / t ^ d) =ᶠ[𝓝[≠] 0]
      (fun t : ℂ => ∑ α ∈ M, ((∑ k, c α k * Φ k (vP + t • h0)) * t ^ (∑ q, α q - d) *
        wz (vP + t • h0) ^ (∑ q, α q + (T - ∑ q, α q))) *
        ∏ q, (t⁻¹ * (σ q (vP + t • h0) / wz (vP + t • h0))) ^ α q) := by
    filter_upwards [hwne, self_mem_nhdsWithin] with t hwt ht
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [sum_mul_pow_mul_prod_eq_div_pow α (c α) (fun k => Φ k (vP + t • h0)) (fun q => σ q (vP + t • h0))
      (wz (vP + t • h0)) t T d ht hwt (fun ⟨k, hk⟩ => hlow α hα k hk)]
  obtain ⟨C, hC⟩ := hb
  have hzero : Tendsto (fun t : ℂ => (∑ α ∈ M, ∑ k, c α k * (∏ q, σ q (vP + t • h0) ^ α q) *
        wz (vP + t • h0) ^ (T - ∑ q, α q) * Φ k (vP + t • h0)) / t ^ d) (𝓝[≠] 0) (𝓝 0) := by
    have hbd : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖(∑ α ∈ M, ∑ k, c α k * (∏ q, σ q (vP + t • h0) ^ α q) *
        wz (vP + t • h0) ^ (T - ∑ q, α q) * Φ k (vP + t • h0)) / t ^ d‖ ≤
        C * ‖h0‖ ^ m * ‖t‖ ^ (m - d) := by
      filter_upwards [hl1.eventually hC, self_mem_nhdsWithin] with t h1 ht
      have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
      rw [add_sub_cancel_left, norm_smul] at h1
      rw [norm_div, norm_pow, div_le_iff₀ (pow_pos htn d)]
      calc _ ≤ C * (‖t‖ * ‖h0‖) ^ m := h1
        _ = C * ‖h0‖ ^ m * ‖t‖ ^ (m - d) * ‖t‖ ^ d := by
          rw [mul_pow, show ‖t‖ ^ m = ‖t‖ ^ (m - d) * ‖t‖ ^ d by
            rw [← pow_add, Nat.sub_add_cancel hdm.le]]
          ring
    refine squeeze_zero_norm' hbd ?_
    have h3 : Tendsto (fun t : ℂ => C * ‖h0‖ ^ m * ‖t‖ ^ (m - d)) (𝓝 0) (𝓝 (C * ‖h0‖ ^ m * ‖(0 : ℂ)‖ ^ (m - d))) :=
      ((continuous_norm.pow _).const_mul _).tendsto 0
    rw [norm_zero, zero_pow (Nat.sub_ne_zero_of_lt hdm), mul_zero] at h3
    exact h3.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hlim (hzero.congr' heq)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem coeff_eq_zero_of_monomial_sum_eq_zero {n : ℕ} (M : Finset (Fin n → ℕ)) (B : (Fin n → ℕ) → ℂ)
    (h : ∀ y : V n, ∑ α ∈ M, B α * ∏ q, y q ^ α q = 0) : ∀ α ∈ M, B α = 0 := by
  classical
  let P : MvPolynomial (Fin n) ℂ :=
    ∑ α ∈ M, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) (B α)
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro y
    have hy := h (WithLp.toLp 2 y)
    simp only at hy
    simp only [P, map_zero, map_sum, MvPolynomial.eval_monomial]
    rw [← hy]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp
  intro α hα
  have hc := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm α)) hP
  simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero,
    (Finsupp.equivFunOnFinite).symm.injective.eq_iff] at hc
  rwa [Finset.sum_ite_eq' M α B, if_pos hα] at hc

theorem leadM_coeff_eq_zero : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (T a δ : ℕ),
    ∀ (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsSec G (t k)) →
    (∀ u : Fin δ → ℂ, (∀ j, ∑ k, u k * t k (Fl.xs j) = 0) → u = 0) →
    ∀ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ,
      (∀ j, (fun z : V (nd X) => leadM X Fl.s Fl.w0 t T a cc (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ a) →
      ∀ α ∈ multiLt (nd X) a, ∀ k, cc α k = 0 := by
  classical
  intro r X Xa Fl G T a δ t ht hind cc hO
  by_contra hne
  push Not at hne
  obtain ⟨α1, hα1, k1, hk1⟩ := hne
  set S := (multiLt (nd X) a).filter (fun α => ∃ k, cc α k ≠ 0) with hSdef
  have hS : S.Nonempty := ⟨α1, Finset.mem_filter.2 ⟨hα1, k1, hk1⟩⟩
  obtain ⟨α0, hα0S, hα0d⟩ := Finset.exists_mem_eq_inf' hS (fun α => ∑ q, α q)
  set d := S.inf' hS (fun α => ∑ q, α q) with hd
  have hα0M := (Finset.mem_filter.1 hα0S).1
  have hlow : ∀ α ∈ multiLt (nd X) a, ∀ k, cc α k ≠ 0 → d ≤ ∑ q, α q := fun α hα k hk =>
    Finset.inf'_le _ (Finset.mem_filter.2 ⟨hα, k, hk⟩)
  have hda : d < a := hα0d ▸ mem_multiLt.1 hα0M
  have key : ∀ j, ∀ α ∈ multiLt (nd X) a, ∑ q, α q = d → ∑ k, cc α k * t k (Fl.xs j) = 0 := by
    intro j
    have hdomo := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X
    have hcd : Differentiable ℂ (cpt X (Fl.xs j)) :=
      (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.cd_cpt X (Fl.xs j)).differentiable (by simp)
    have hc0 : cpt X (Fl.xs j) 0 = Fl.xs j := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero X (Fl.xs j)
    have hUo : IsOpen (cpt X (Fl.xs j) ⁻¹' X.dom) := hdomo.preimage hcd.continuous
    have h0U : (0 : V (nd X)) ∈ cpt X (Fl.xs j) ⁻¹' X.dom := by
      simp only [Set.mem_preimage, hc0]
      exact Fl.xs_mem j
    have hcomp : ∀ P : Frame X.Ψ r → ℂ, DifferentiableOn ℂ P X.dom →
        DifferentiableOn ℂ (fun z => P (cpt X (Fl.xs j) z)) (cpt X (Fl.xs j) ⁻¹' X.dom) :=
      fun P hP z hz => ((hP.differentiableAt (hdomo.mem_nhds hz)).comp z
        (hcd z)).differentiableWithinAt
    have hs0 : ∀ k, Fl.s k (Fl.xs j) = 0 := by
      refine (Fl.S_eq (Fl.xs j) (Fl.xs_mem j)).2 ⟨j, 1, X.Γ.one_mem, nmat X 0, ?_, ?_⟩
      · intro τ
        have hm := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.nmat_zero X τ
        refine ⟨by rw [hm]; simp, fun p c hpc => ?_⟩
        have := congrFun (congrFun hm p) c
        simp only [mat, Matrix.of_apply] at this
        rw [this, Matrix.one_apply_ne (ne_of_gt hpc)]
      · have hr : rmul (Fl.xs j) (nmat X 0) = Fl.xs j := hc0
        rw [hr]
        funext τ
        simp [lact, mat, Matrix.map_one]
        rfl
    have main := fun h0 => lowest_degree (cpt X (Fl.xs j) ⁻¹' X.dom) hUo 0 h0U
      (fun q z => Fl.s q (cpt X (Fl.xs j) z)) (fun z => Fl.w0 (cpt X (Fl.xs j) z))
      (fun k z => t k (cpt X (Fl.xs j) z)) (multiLt (nd X) a) T a d cc
      (fun q => hcomp _ (Fl.s_van q).1.1.1.1) (hcomp _ Fl.weightForm_vanishes.1.1.1.1)
      (fun k => hcomp _ (ht k).1) (fun q => by simp only [hc0, hs0])
      (by simp only [hc0]; exact Fl.w0_ne j) hlow hda
      (by
        obtain ⟨C, hC⟩ := (hO j).bound
        refine ⟨C, hC.mono fun z hz => ?_⟩
        simpa [leadM, monoM, norm_pow] using hz) h0
    simp only [hc0] at main
    have hsurj := ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 (Fl.coord j)))).2
    have hB := coeff_eq_zero_of_monomial_sum_eq_zero (multiLt (nd X) a)
      (fun α => (∑ k, cc α k * t k (Fl.xs j)) * 0 ^ (∑ q, α q - d) *
        Fl.w0 (Fl.xs j) ^ (∑ q, α q + (T - ∑ q, α q))) (fun y => by
          obtain ⟨h0, hh0⟩ := hsurj y
          have := main h0
          rw [← hh0]
          exact this)
    intro α hα hαd
    have := hB α hα
    rw [hαd, Nat.sub_self, pow_zero, mul_one] at this
    exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (Fl.w0_ne j))
  have hu : cc α0 = 0 := hind (cc α0) (fun j => key j α0 hα0M hα0d.symm)
  obtain ⟨k, hk⟩ := (Finset.mem_filter.1 hα0S).2
  exact hk (congrFun hu k)

end GlobalTheory.LeadIndep
