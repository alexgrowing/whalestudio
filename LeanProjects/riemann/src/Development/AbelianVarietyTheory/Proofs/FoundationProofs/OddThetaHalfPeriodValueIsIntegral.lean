import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniquenessStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Topology
open Filter

namespace GlobalTheory.HalfPeriodValue

lemma second_order {f f' a s b : ℂ → ℂ} {c : ℂ} (hf : ∀ᶠ z in 𝓝 (0 : ℂ), HasDerivAt f (f' z) z)
    (hf' : HasDerivAt f' c 0) (h0 : f 0 = 0) (h0' : f' 0 = 0) (ha : Differentiable ℂ a)
    (hs : Differentiable ℂ s) (hb : Differentiable ℂ b) (hs0 : s 0 = 0) (hs1 : deriv s 0 = 1)
    (h : ∀ᶠ z in 𝓝 (0 : ℂ), f z * a z = s z ^ 2 * b z) : c * a 0 = 2 * b 0 := by
  have d : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → Differentiable ℂ (deriv g) := fun hg =>
    differentiableOn_univ.1 (hg.differentiableOn.deriv isOpen_univ)
  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), f' z * a z + f z * deriv a z =
      (2 * s z * deriv s z) * b z + (s z * s z) * deriv b z := by
    filter_upwards [hf, h.eventually_nhds] with z hz hz'
    have e1 := hz.mul (ha z).hasDerivAt
    have e2 := ((hs z).hasDerivAt.mul (hs z).hasDerivAt).mul (hb z).hasDerivAt
    have e3 := e1.unique (e2.congr_of_eventuallyEq (by
      filter_upwards [hz'] with w hw
      simpa [sq] using hw))
    simp only [Pi.mul_apply] at e3
    linear_combination e3
  have e1 := (hf'.mul (ha 0).hasDerivAt).add (hf.self_of_nhds.mul (d ha 0).hasDerivAt)
  have e2 := ((((hs 0).hasDerivAt.const_mul 2).mul (d hs 0).hasDerivAt).mul (hb 0).hasDerivAt).add
    (((hs 0).hasDerivAt.mul (hs 0).hasDerivAt).mul (d hb 0).hasDerivAt)
  have e3 := e1.unique (e2.congr_of_eventuallyEq (by
      filter_upwards [h1] with w hw
      simpa using hw))
  simp only [Pi.mul_apply, h0, h0', hs0, hs1] at e3
  linear_combination e3

lemma isIntegral_of_eq {u j : ℂ} (hj : IsIntegral ℤ j) (h : (u ^ 12 + 16) ^ 3 = j * u ^ 12) :
    IsIntegral ℤ u := by
  refine IsIntegral.of_pow (n := 12) (by norm_num) ?_
  let R := integralClosure ℤ ℂ
  refine isIntegral_trans (A := R) _ ?_
  refine ⟨(Polynomial.X + 16) ^ 3 - Polynomial.C (⟨j, hj⟩ : R) * Polynomial.X, by monicity!, ?_⟩
  rw [← Polynomial.aeval_def]
  simp only [map_sub, map_pow, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_ofNat]
  exact sub_eq_zero.2 h

theorem value_half_period : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → TaylorLogMetric.discr Λ = 1 → IsIntegral ℤ (1728 * g2 Λ ^ 3) → ∀ t, 2 * t ∈ Λ → t ∉ Λ → U1 Λ t (sgStar Λ) 0 ≠ 0 ∧ IsIntegral ℤ (U1 Λ t (sgStar Λ) 0) ∧ U1 Λ t (sgStar Λ) 0 ^ 8 = 16 * (g2 Λ - 3 * wpF Λ t ^ 2) ∧ 4 * wpF Λ t ^ 3 - g2 Λ * wpF Λ t - g3 Λ = 0 := by
  intro Λ hΛ hΔ hj t h2 ht
  obtain ⟨⟨hd, hd1, hodd, hU⟩, hzero, -, hwp, -⟩ := GlobalTheory.T.oddThetaFunction_existence_uniqueness Λ hΛ
  obtain ⟨w₁, w₂, hli, hΛ⟩ := hΛ
  let L : PeriodPair := ⟨w₁, w₂, hli⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := fun z => by
    rw [hΛ, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
    simp [L]
  obtain ⟨hg2, hg3, -, -, hw, -⟩ := GlobalTheory.T.latticeInvariants_periodPair_dictionary L Λ hL
  have htL : t ∉ L.lattice := fun h => ht ((hL t).2 h)
  have hP' : L.derivWeierstrassP t = 0 := by
    have e1 := L.derivWeierstrassP_add_coe (-t) ⟨2 * t, (hL _).1 h2⟩
    rw [L.derivWeierstrassP_neg] at e1
    have : -t + 2 * t = t := by ring
    simp only [this] at e1
    linear_combination e1 / 2
  have hcub : 4 * wpF Λ t ^ 3 - g2 Λ * wpF Λ t - g3 Λ = 0 := by
    rw [(hw t ht).1, hg2, hg3, ← L.derivWeierstrassP_sq t htL, hP']
    simp
  set k : ℂ := (Real.pi : ℂ) * (starRingEnd ℂ) t / (area Λ : ℂ) with hk
  have hsys := GlobalTheory.weierstrass_system_add_const L t (z := 0) (by simpa using htL)
  have key := second_order (f := fun z => L.weierstrassP (z + t) - L.weierstrassP t)
    (f' := fun z => L.derivWeierstrassP (z + t))
    (a := fun z => sgStar Λ (z + t) ^ 2 * sgStar Λ t ^ 2) (s := sgStar Λ)
    (b := fun z => Complex.exp (2 * k * z + 2 * k * t))
    (hsys.mono fun z hz => hz.1.sub_const _) hsys.self_of_nhds.2 (by simp) (by simpa using hP')
    (by fun_prop) hd (by fun_prop) ((hzero 0).2 Λ.zero_mem) hd1 (by
      filter_upwards [(continuous_add_const t).continuousAt.eventually
        (GlobalTheory.eventually_notMem_periodLattice L (z := 0 + t) (by simpa using htL))] with z hz
      have hz' : z + t ∉ Λ := fun h => hz ((hL _).1 h)
      have e1 := hwp (z + t) t hz' ht
      rw [(hw _ hz').1, (hw t ht).1] at e1
      have e2 := hU (2 * t) h2 z
      rw [if_neg (by simpa using ht)] at e2
      have e3 : -(Real.pi : ℂ) * z * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
          (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ)) =
          -(2 * k * z + 2 * k * t) := by
        rw [hk, map_mul, map_ofNat]; ring
      simp only [U1] at e2
      rw [e3, Complex.exp_neg] at e2
      have e4 : z + t + t = z + 2 * t := by ring
      rw [e1, e4, add_sub_cancel_right]
      have e5 := Complex.exp_ne_zero (2 * k * z + 2 * k * t)
      rw [mul_inv_eq_iff_eq_mul₀ e5] at e2
      rw [e2]; ring)
  simp only [zero_add, mul_zero] at key
  rw [← (hw t ht).1, ← hg2] at key
  have hu : U1 Λ t (sgStar Λ) 0 ^ 4 * Complex.exp (2 * k * t) = sgStar Λ t ^ 4 := by
    simp only [U1, zero_add]
    rw [mul_pow, mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have : ((4 : ℕ) : ℂ) * (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) t / (area Λ : ℂ) -
      (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) + 2 * k * t = 0 := by
      rw [hk]; push_cast; ring
    rw [this, Complex.exp_zero, mul_one]
  set u := U1 Λ t (sgStar Λ) 0
  set e := wpF Λ t
  have h4 : (12 * e ^ 2 - g2 Λ) * u ^ 4 = 4 := by
    apply mul_right_cancel₀ (Complex.exp_ne_zero (2 * k * t))
    linear_combination 2 * key + (12 * e ^ 2 - g2 Λ) * hu
  have hD : (12 * e ^ 2 - g2 Λ) ^ 2 * (g2 Λ - 3 * e ^ 2) = 1 := by
    have h3 : g3 Λ = 4 * e ^ 3 - g2 Λ * e := by linear_combination -hcub
    rw [← hΔ, TaylorLogMetric.discr, h3]; ring
  have h8 : u ^ 8 = 16 * (g2 Λ - 3 * e ^ 2) := by
    linear_combination (-u ^ 8) * hD +
      (g2 Λ - 3 * e ^ 2) * ((12 * e ^ 2 - g2 Λ) * u ^ 4 + 4) * h4
  refine ⟨fun h => by simp [h] at h4, isIntegral_of_eq hj ?_, h8, hcub⟩
  have h5 : u ^ 12 + 16 = 12 * g2 Λ * u ^ 4 := by
    linear_combination u ^ 4 * h8 - 4 * h4
  rw [h5]; ring

end GlobalTheory.HalfPeriodValue
