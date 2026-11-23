import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

noncomputable section

namespace GlobalTheory.WpSeries

abbrev tay (f : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk (coef1 f)

variable {f g : ℂ → ℂ}

lemma tay_congr (h : f =ᶠ[𝓝 0] g) : tay f = tay g := by
  ext n
  simp only [PowerSeries.coeff_mk, coef1, h.iteratedDeriv_eq n]

lemma tay_congr' (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (h : f =ᶠ[𝓝[≠] 0] g) :
    tay f = tay g :=
  tay_congr ((hf.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg.continuousAt).1 h)

lemma tay_add (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z + g z) = tay f + tay g := by
  ext n
  simp only [map_add, PowerSeries.coeff_mk, coef1, ← add_div]
  congr 1
  exact iteratedDeriv_add hf.contDiffAt hg.contDiffAt

lemma tay_sub (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z - g z) = tay f - tay g := by
  ext n
  simp only [map_sub, PowerSeries.coeff_mk, coef1, ← sub_div]
  congr 1
  exact iteratedDeriv_sub hf.contDiffAt hg.contDiffAt

lemma tay_mul (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z * g z) = tay f * tay g := by
  ext n
  have h : iteratedDeriv n (fun z => f z * g z) 0 = _ :=
    iteratedDeriv_mul (n := n) hf.contDiffAt hg.contDiffAt
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, coef1, h]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have e : ((n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ)) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have h1 : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (n - i).factorial_ne_zero
  have h3 : (n.choose i : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hi').ne'
  rw [← e]
  field_simp

lemma constantCoeff_tay (f : ℂ → ℂ) : PowerSeries.constantCoeff (tay f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  simp [coef1]

lemma tay_const (c : ℂ) : tay (fun _ => c) = PowerSeries.C c := by
  ext n
  rcases n with _ | n
  · simp [coef1]
  · simp [coef1, iteratedDeriv_const]

lemma tay_deriv (f : ℂ → ℂ) : tay (deriv f) = PowerSeries.derivativeFun (tay f) := by
  ext n
  refine Eq.trans ?_ (PowerSeries.coeff_derivativeFun (tay f) n).symm
  simp only [PowerSeries.coeff_mk, coef1, iteratedDeriv_succ', Nat.factorial_succ]
  have h1 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

lemma tay_id : tay (fun z => z) = PowerSeries.X := by
  ext n
  rcases n with _ | _ | n
  · simp [coef1]
  · simp [coef1]
  · simp [coef1, iteratedDeriv_succ', iteratedDeriv_const, PowerSeries.coeff_X]

lemma tay_pow (hf : AnalyticAt ℂ f 0) (n : ℕ) : tay (fun z => f z ^ n) = tay f ^ n := by
  induction n with
  | zero => simp [tay_const]
  | succ n ih =>
    simp only [pow_succ]
    rw [tay_mul (hf.fun_pow n) hf, ih]

def sqWp (L : PeriodPair) (z : ℂ) : ℂ := 1 + z ^ 2 * L.weierstrassPExcept 0 z

lemma analyticAt_sqWp (L : PeriodPair) : AnalyticAt ℂ (sqWp L) 0 := by
  have := L.analyticAt_weierstrassPExcept 0
  unfold sqWp
  fun_prop

lemma sqWp_eq (L : PeriodPair) {z : ℂ} (hz : z ≠ 0) : sqWp L z = z ^ 2 * L.weierstrassP z := by
  rw [← L.weierstrassPExcept_add 0, sqWp]
  simp
  field_simp
  ring

lemma eventually_notMem (L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  have h := L.compl_lattice_diff_singleton_mem_nhds 0
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z h1 h2 h3
  exact h1 ⟨h3, h2⟩

lemma deriv_sqWp (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (sqWp L) z = 2 * z * L.weierstrassP z + z ^ 2 * L.derivWeierstrassP z := by
  have h0 : z ≠ 0 := by rintro rfl; exact hz (zero_mem _)
  have h1 : sqWp L =ᶠ[𝓝 z] fun w => w ^ 2 * L.weierstrassP w := by
    filter_upwards [isOpen_ne.mem_nhds h0] with w hw using sqWp_eq L hw
  have h2 : DifferentiableAt ℂ L.weierstrassP z :=
    L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
  rw [h1.deriv_eq, deriv_fun_mul (by fun_prop) h2, L.deriv_weierstrassP]
  simp

lemma isWpSer_sqWp (L : PeriodPair) : IsWpSer L.g₂ L.g₃ (tay (sqWp L)) := by
  have hp := analyticAt_sqWp L
  have hd := hp.deriv
  have hi : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  refine ⟨by rw [constantCoeff_tay]; simp [sqWp], ?_⟩
  have key := tay_congr' (f := fun z => (z * deriv (sqWp L) z - 2 * sqWp L z) ^ 2)
    (g := fun z => 4 * sqWp L z ^ 3 - L.g₂ * z ^ 4 * sqWp L z - L.g₃ * z ^ 6)
    (by fun_prop) (by fun_prop) (by
      filter_upwards [eventually_notMem L, self_mem_nhdsWithin] with z h1 h2
      rw [deriv_sqWp L h1, sqWp_eq L h2]
      linear_combination z ^ 6 * L.derivWeierstrassP_sq z h1)
  rw [tay_pow (by fun_prop), tay_sub (by fun_prop) (by fun_prop),
    tay_sub (by fun_prop) (by fun_prop), tay_sub (by fun_prop) (by fun_prop),
    tay_mul hi hd, tay_mul analyticAt_const hp, tay_mul analyticAt_const (hp.fun_pow 3),
    tay_mul (by fun_prop) hp, tay_mul analyticAt_const (hi.fun_pow 4),
    tay_mul analyticAt_const (hi.fun_pow 6), tay_pow hp, tay_pow hi, tay_pow hi, tay_id,
    tay_deriv, tay_const, tay_const, tay_const, tay_const, map_ofNat, map_ofNat] at key
  exact key

theorem exists_wpSer : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∃ P : PowerSeries ℂ, IsWpSer (g2 Λ) (g3 Λ) P ∧ ∀ v, v ∉ Λ → PowerSeries.X ^ 2 * PowerSeries.mk (coef1 (sqTh Λ v)) = PowerSeries.mk (coef1 (sgStar Λ)) ^ 2 * lineSer P (wpF Λ v) := by
  intro Λ h
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  refine ⟨tay (sqWp L), ?_, fun v hv => ?_⟩
  · rw [GlobalTheory.LatticeInvariants.g2_eq hL, GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL]
    exact isWpSer_sqWp L
  have hp := analyticAt_sqWp L
  have hi : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hs : AnalyticAt ℂ (sgStar Λ) 0 := h.differentiable.analyticAt 0
  have ht : AnalyticAt ℂ (sqTh Λ v) 0 := (h.differentiable_sqTh v).analyticAt 0
  have key := tay_congr' (f := fun z => z ^ 2 * sqTh Λ v z)
    (g := fun z => sgStar Λ z ^ 2 * (sqWp L z - wpF Λ v * z ^ 2))
    (by fun_prop) (by fun_prop) (by
      filter_upwards [eventually_notMem L, self_mem_nhdsWithin] with z h1 h2
      rw [h.sqTh_eq hv ((hL z).not.2 h1), sqWp_eq L h2, GlobalTheory.LatticeInvariants.wpF_eq hL z]
      ring)
  rw [tay_mul (hi.fun_pow 2) ht, tay_mul (hs.fun_pow 2) (by fun_prop), tay_sub hp (by fun_prop),
    tay_mul analyticAt_const (hi.fun_pow 2), tay_pow hi, tay_pow hs, tay_id, tay_const] at key
  exact key

end GlobalTheory.WpSeries
