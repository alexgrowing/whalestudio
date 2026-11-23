import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem realFlowPeriods_span_eq_top {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) :
    Submodule.span ℝ {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
      p = fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re} = ⊤ := by
  classical
  have hNpos : (0 : ℝ) < ((X.m * X.chiOrd la : ℕ) : ℝ) := by
    have h1 : 0 < X.m := X.m_pos
    have h2 : 0 < X.chiOrd la := (X.χ_fin la).choose_spec.1
    exact_mod_cast Nat.mul_pos h1 h2
  have hD := integerApproximationCount_holds (E := E)
  unfold IntegerApproximationCount at hD
  obtain ⟨happrox, -⟩ := hD r X
  have hadd : ∀ x y : E, cc (x + y) = cc x + cc y := by
    intro x y
    unfold cc
    exact map_add _ x y
  rw [eq_top_iff]
  intro v _
  rw [← SetLike.mem_coe]
  apply (Submodule.closed_of_finiteDimensional _).closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  set N : ℝ := ((X.m * X.chiOrd la : ℕ) : ℝ) with hN
  set B : ℝ := 2 * (fdeg E : ℝ) ^ 2 * rdE E with hB
  set t : ℝ := (|B| + 1) / ε with ht
  have htpos : 0 < t := div_pos (by positivity) hε
  have hεt : ε * t = |B| + 1 := by
    rw [ht]
    field_simp
  obtain ⟨α, hα⟩ := happrox (fun τ => ((t * v τ : ℝ) : ℂ))
  set a : E := (α : E) + cc (α : E) with ha
  have hcca : cc a = a := by
    rw [ha, hadd, cc_cc, add_comm]
  have hinta : IsIntegral ℤ a := by
    have h0 : IsIntegral ℤ (α : E) := NumberField.RingOfIntegers.isIntegral_coe α
    exact h0.add (isIntegral_cc h0)
  have hre : ∀ τ : X.Ψ, (τ.1 a).re = 2 * (τ.1 (α : E)).re := by
    intro τ
    rw [ha, map_add, emb_cc, Complex.add_re, Complex.conj_re]
    ring
  refine ⟨(1 / (2 * N * t)) • (fun τ : X.Ψ => N * (τ.1 a).re), ?_, ?_⟩
  · rw [SetLike.mem_coe]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨a, hcca, hinta, rfl⟩
  · rw [dist_eq_norm]
    have hlt : ∀ τ : X.Ψ,
        ‖(v - (1 / (2 * N * t)) • (fun τ : X.Ψ => N * (τ.1 a).re)) τ‖ < ε := by
      intro τ
      have hval : (v - (1 / (2 * N * t)) • (fun τ : X.Ψ => N * (τ.1 a).re)) τ
          = (t * v τ - (τ.1 (α : E)).re) / t := by
        have hN0 : N ≠ 0 := hNpos.ne'
        have ht0 : t ≠ 0 := htpos.ne'
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hre]
        field_simp <;> ring
      rw [hval, Real.norm_eq_abs, abs_div, abs_of_pos htpos, div_lt_iff₀ htpos]
      have h1 : |t * v τ - (τ.1 (α : E)).re| ≤ ‖τ.1 (α : E) - ((t * v τ : ℝ) : ℂ)‖ := by
        have h := Complex.abs_re_le_norm (τ.1 (α : E) - ((t * v τ : ℝ) : ℂ))
        rw [Complex.sub_re, Complex.ofReal_re] at h
        rw [abs_sub_comm]
        exact h
      have h2 : ‖τ.1 (α : E) - ((t * v τ : ℝ) : ℂ)‖ ≤ B := hα τ
      linarith [le_abs_self B]
    exact (pi_norm_lt_iff hε).2 hlt

theorem spectralGap_holds : CuspFormGapCondition (E := E) := by
  classical
  unfold CuspFormGapCondition
  intro r X la P hP
  have hP' : X.IsBddSec la P ∧ ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, X.fj la ξ 0 P x = 0 := hP
  have hB : X.IsSec la P ∧ ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C := hP'.1
  obtain ⟨C, hC⟩ := hB.2
  have hm3 := moderateCoefficientPositivity_holds (E := E)
  unfold ModerateCoefficientPositivity at hm3
  have hnn := (hm3 r X la P C 0 hB.1 (fun x hx => by simpa using hC x hx)).1
  have hspan := realFlowPeriods_span_eq_top X la
  obtain ⟨T, hTS, hTspan, hTli⟩ := exists_linearIndependent ℝ
    {p : X.Ψ → ℝ | ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧
      p = fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re}
  rw [hspan] at hTspan
  have hTfin : T.Finite := hTli.setFinite
  set M : ℝ := ∑ p ∈ hTfin.toFinset, ∑ σ, |p σ| with hM
  have hM0 : 0 ≤ M :=
    Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun σ _ => abs_nonneg (p σ)))
  have hcpos : (0 : ℝ) < 1 / (2 * M + 2) := div_pos one_pos (by linarith)
  refine ⟨1 / (2 * M + 2), hcpos, ?_⟩
  show P ∈ X.SS la ∧ ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∑ τ, ν τ ≤ 1 / (2 * M + 2) →
    ∀ x ∈ X.dom, X.fj la ξ ν P x = 0
  refine ⟨hP, ?_⟩
  intro ξ hξ ν hν x hx
  by_contra hne
  have hint : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k := by
    by_contra hc
    apply hne
    rw [Data.fj, if_neg hc]
  have hpos : ∀ τ, 0 ≤ ν τ := hnn ξ hξ ν x hx hne
  have hsmall : ∀ τ, ν τ ≤ 1 / (2 * M + 2) := fun τ =>
    le_trans (Finset.single_le_sum (fun σ _ => hpos σ) (Finset.mem_univ τ)) hν
  have hzero : ∀ p ∈ T, ∑ σ, ν σ * p σ = 0 := by
    intro p hp
    obtain ⟨k, hk⟩ := hint p (AddSubgroup.subset_closure (hTS hp))
    have hpM : ∑ σ, |p σ| ≤ M :=
      Finset.single_le_sum (f := fun q : X.Ψ → ℝ => ∑ σ, |q σ|)
        (fun q _ => Finset.sum_nonneg (fun σ _ => abs_nonneg (q σ))) (hTfin.mem_toFinset.2 hp)
    have habs : |∑ σ, ν σ * p σ| ≤ 1 / (2 * M + 2) * M := by
      calc |∑ σ, ν σ * p σ| ≤ ∑ σ, |ν σ * p σ| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ σ, 1 / (2 * M + 2) * |p σ| := by
          apply Finset.sum_le_sum
          intro σ _
          rw [abs_mul, abs_of_nonneg (hpos σ)]
          exact mul_le_mul_of_nonneg_right (hsmall σ) (abs_nonneg _)
        _ = 1 / (2 * M + 2) * ∑ σ, |p σ| := by simp only [Finset.mul_sum]
        _ ≤ 1 / (2 * M + 2) * M := mul_le_mul_of_nonneg_left hpM hcpos.le
    have hfrac : 2 * (1 / (2 * M + 2) * M) < 1 := by
      rw [show 2 * (1 / (2 * M + 2) * M) = (2 * M) / (2 * M + 2) by ring,
        div_lt_one (by linarith)]
      linarith
    have hlt : |(k : ℝ)| < 1 := by
      rw [← hk, abs_mul, abs_two]
      linarith
    have hk0 : k = 0 := by
      have h := abs_lt.1 hlt
      have h1 : -1 < k := by exact_mod_cast h.1
      have h2 : k < 1 := by exact_mod_cast h.2
      omega
    rw [hk0, Int.cast_zero] at hk
    linarith
  let f : (X.Ψ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun q => ∑ σ, ν σ * q σ
      map_add' := fun q q' => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c q => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun σ _ => by ring) }
  have hle : Submodule.span ℝ T ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    intro p hp
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hzero p hp
  have hmem : ν ∈ Submodule.span ℝ T := by
    rw [hTspan]
    exact Submodule.mem_top
  have hsq : ∑ σ, ν σ * ν σ = 0 := LinearMap.mem_ker.1 (hle hmem)
  have hν0 : ν = 0 := by
    funext σ
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (ν i))).1 hsq σ
      (Finset.mem_univ σ)
    simpa using mul_self_eq_zero.1 h
  subst hν0
  exact hne (hP'.2 ξ hξ x hx)

end ReciprocityTheory.ChartRestriction.G.FD
