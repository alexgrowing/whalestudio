import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaTwoMulAtZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.HalfPeriodValue

open Filter Topology

theorem U1_sgStar_pow_eight : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t : ℂ, t ∉ Λ → 2 * t ∈ Λ →
    U1 Λ t (sgStar Λ) 0 ^ 8 * ((wpF Λ t ^ 2 + g2 Λ / 4) ^ 2 + 2 * g3 Λ * wpF Λ t) = 1 := by
  intro Λ hΛ t ht h2t
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have laws := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  have hd : Differentiable ℂ (sgStar Λ) := laws.1.1
  have hd0 : deriv (sgStar Λ) 0 = 1 := laws.1.2.1
  have hz0 : sgStar Λ 0 = 0 := (laws.2.1 0).2 Λ.zero_mem
  have hzw : sgStar Λ (2 * t) = 0 := (laws.2.1 _).2 h2t
  have htL : t ∉ L.lattice := fun h => ht ((hL t).2 h)
  have hD0 : L.derivWeierstrassP t = 0 :=
    (GlobalTheory.derivWeierstrassP_eq_zero_iff L htL).2 (by rw [← two_mul]; exact (hL _).1 h2t)

  have hA : HasDerivAt (fun z => sgStar Λ (2 * z)) (deriv (sgStar Λ) (2 * t) * 2) t := by
    have := (hd (2 * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul (2 : ℂ))
    rw [mul_one] at this
    exact this
  have hB : HasDerivAt (fun z => -(L.derivWeierstrassP z) * sgStar Λ z ^ 4)
      (-(6 * L.weierstrassP t ^ 2 - L.g₂ / 2) * sgStar Λ t ^ 4 +
        -(L.derivWeierstrassP t) * ((4 : ℕ) * sgStar Λ t ^ (4 - 1) * deriv (sgStar Λ) t)) t :=
    (GlobalTheory.hasDerivAt_derivWeierstrassP L htL).neg.mul ((hd t).hasDerivAt.pow 4)
  have hev : (fun z => sgStar Λ (2 * z)) =ᶠ[𝓝 t] (fun z => -(L.derivWeierstrassP z) * sgStar Λ z ^ 4) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds htL] with z hz
    have hz' : z ∉ Λ := fun h => hz ((hL z).1 h)
    rw [GlobalTheory.SigmaDuplication.sgStar_two_mul hΛ hz', GlobalTheory.LatticeInvariants.wpD_eq hL z]
  have hu := hA.unique (hB.congr_of_eventuallyEq hev)
  rw [hD0] at hu

  set s : ℂ := if 2 * t / 2 ∈ Λ then 1 else -1 with hs
  have hfun : U1 Λ (2 * t) (sgStar Λ) = fun z => s * sgStar Λ z := funext (hΛ.sg_law h2t)
  have hE : Differentiable ℂ (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ)))) := by fun_prop
  have hC : HasDerivAt (U1 Λ (2 * t) (sgStar Λ))
      (deriv (sgStar Λ) (0 + 2 * t) * Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ))) +
        sgStar Λ (0 + 2 * t) * deriv (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ)))) 0) 0 :=
    ((hd _).hasDerivAt.comp_add_const 0 (2 * t)).mul (hE 0).hasDerivAt
  have hC' : HasDerivAt (U1 Λ (2 * t) (sgStar Λ)) (s * 1) 0 := by
    rw [hfun, ← hd0]; exact (hd 0).hasDerivAt.const_mul s
  have hv := hC.unique hC'
  rw [zero_add, hzw] at hv
  have hs2 : s ^ 2 = 1 := by rw [hs]; split_ifs <;> norm_num
  have hU : U1 Λ t (sgStar Λ) 0 = sgStar Λ t * Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) := by
    simp only [U1, zero_add]
    congr 1
    congr 1
    ring
  have hexp : Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) (2 * t) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * (area Λ : ℂ))) =
      Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) ^ 4 := by
    rw [← Complex.exp_nat_mul, map_mul, map_ofNat]
    congr 1
    push_cast
    ring
  rw [hexp] at hv
  have key : U1 Λ t (sgStar Λ) 0 ^ 4 * (6 * L.weierstrassP t ^ 2 - L.g₂ / 2) = -2 * s := by
    rw [hU, mul_pow]
    linear_combination (Complex.exp (-(Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * (area Λ : ℂ))) ^ 4) * hu - 2 * hv

  have hcub : 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ = 0 := by
    have := L.derivWeierstrassP_sq t htL
    rw [hD0] at this
    linear_combination -this
  obtain ⟨hg2, hg3, -, -, hw, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  rw [hg2, hg3, (hw t ht).1]
  linear_combination (1 / 4 : ℂ) * (U1 Λ t (sgStar Λ) 0 ^ 4 * (6 * L.weierstrassP t ^ 2 - L.g₂ / 2) - 2 * s) * key
    + hs2 - 2 * L.weierstrassP t * U1 Λ t (sgStar Λ) 0 ^ 8 * hcub

end GlobalTheory.HalfPeriodValue
