import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

variable {Λ : AddSubgroup ℂ}

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma sgStar_add_lattice_eq_mul_exp (hΛ : _root_.GlobalTheory.EvenTheta.IsLat Λ) {a : ℂ} (ha : a ∈ Λ)
    (z : ℂ) :
    _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ (z + a) = (if a / 2 ∈ Λ then 1 else -1) * _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ z *
      Complex.exp (↑Real.pi * z * (starRingEnd ℂ) a / ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ) +
        ↑Real.pi * a * (starRingEnd ℂ) a / (2 * ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ))) := by
  have h := hΛ.sg_law ha z
  unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1 at h
  rw [← h, mul_assoc, ← Complex.exp_add]
  ring_nf <;> simp

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma mul_exp_eq_one_of_exp_relation {ε s x y w k : ℂ} (hs : s ≠ 0)
    (h : -1 * s * Complex.exp x = ε * (-1 * s * Complex.exp y) * Complex.exp w)
    (hk : y + w = x + k) : ε * Complex.exp k = 1 := by
  have h' : -1 * s * Complex.exp x = ε * (-1 * s * (Complex.exp x * Complex.exp k)) := by
    rw [← Complex.exp_add, ← hk, Complex.exp_add]
    linear_combination h
  have hprod : (s * Complex.exp x) * (ε * Complex.exp k - 1) = 0 := by
    linear_combination h'
  rcases mul_eq_zero.1 hprod with h0 | h0
  · exact absurd h0 (mul_ne_zero hs (Complex.exp_ne_zero x))
  · exact sub_eq_zero.1 h0

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in
private lemma mul_mul_exp_eq_of_mul_exp_eq_one {ε k a s q : ℂ} (h : ε * Complex.exp k = 1) (hs : s = k + q) :
    ε * (a * Complex.exp s) = a * Complex.exp q := by
  rw [hs, Complex.exp_add]
  linear_combination (a * Complex.exp q) * h

open NumberField Classical in
open scoped BigOperators in
variable {Λ : AddSubgroup ℂ} in

theorem _root_.GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties : ∀ Λ : AddSubgroup ℂ, _root_.GlobalTheory.EvenTheta.IsLat Λ →
    ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → Differentiable ℂ (_root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀) ∧ _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ 0 = 1 ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ (-z) = _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z) ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z ^ 2 = _root_.GlobalTheory.EvenTheta.sqTh Λ t₀ z) ∧
    (∀ z, _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z = 0 ↔ z + t₀ ∈ Λ) ∧
    ∀ ω ∈ Λ, ω / 2 + t₀ ∉ Λ → ∀ z, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ ω (_root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀) z = _root_.Formalism.MainNotions.GL3Theta.th0 Λ t₀ z := by
  intro Λ hΛ t ht h2t
  have hσt : _root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ t ≠ 0 := fun h => ht ((hΛ.sg_eq_zero t).1 h)
  have hhalf : ¬ (2 * t / 2 ∈ Λ) := by rwa [mul_div_cancel_left₀ t two_ne_zero]
  have hU0 : _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) 0 ≠ 0 := by
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [zero_add]
    exact mul_ne_zero hσt (Complex.exp_ne_zero _)
  have hopp : ∀ y, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ (-t) (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) y = -_root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) y := by
    intro y
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [show y + t = y + -t + 2 * t by ring, sgStar_add_lattice_eq_mul_exp hΛ h2t, if_neg hhalf]
    simp only [mul_assoc, ← Complex.exp_add, map_neg, map_mul, map_ofNat]
    ring_nf
  have heven : ∀ z, _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) (-z) = _root_.Formalism.MainNotions.TaylorLogMetric.U1 Λ t (_root_.Formalism.MainNotions.TaylorLogMetric.sgStar Λ) z := by
    intro z
    have h := hopp z
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1 at h ⊢
    rw [show -z + t = -(z + -t) by ring, hΛ.sg_neg]
    simp only [map_neg] at h ⊢
    ring_nf at h ⊢
    linear_combination -h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hd := hΛ.differentiable
    unfold _root_.Formalism.MainNotions.GL3Theta.th0 _root_.Formalism.MainNotions.TaylorLogMetric.U1
    fun_prop
  · unfold _root_.Formalism.MainNotions.GL3Theta.th0
    exact div_self hU0
  · intro z
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [heven]
  · intro z
    have h := hΛ.sqTh_mul ht z
    rw [hopp, hopp] at h
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hU0)]
    linear_combination h
  · intro z
    unfold _root_.Formalism.MainNotions.GL3Theta.th0
    rw [div_eq_zero_iff, or_iff_left hU0]
    unfold _root_.Formalism.MainNotions.TaylorLogMetric.U1
    rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), hΛ.sg_eq_zero]
  · intro ω hω hωt z
    have hsum : ¬ ((ω + 2 * t) / 2 ∈ Λ) := by
      rwa [show (ω + 2 * t) / 2 = ω / 2 + t by ring]
    have h1 := sgStar_add_lattice_eq_mul_exp hΛ (add_mem hω h2t) t
    have h2 := sgStar_add_lattice_eq_mul_exp hΛ hω (t + 2 * t)
    have h3 := sgStar_add_lattice_eq_mul_exp hΛ h2t t
    rw [if_neg hsum] at h1
    rw [if_neg hhalf] at h3
    rw [show t + 2 * t + ω = t + (ω + 2 * t) by ring, h1, h3] at h2
    have hε := mul_exp_eq_one_of_exp_relation
      (k := (↑Real.pi * t * (starRingEnd ℂ) ω - ↑Real.pi * ω * (starRingEnd ℂ) t) /
        ↑(_root_.Formalism.MainNotions.TaylorLogMetric.area Λ)) hσt h2 (by simp only [map_add, map_mul, map_ofNat]; ring)
    unfold _root_.Formalism.MainNotions.GL3Theta.th0 _root_.Formalism.MainNotions.TaylorLogMetric.U1
    beta_reduce
    rw [show z + ω + t = z + t + ω by ring, sgStar_add_lattice_eq_mul_exp hΛ hω, div_mul_eq_mul_div]
    congr 1
    simp only [mul_assoc, ← Complex.exp_add]
    exact mul_mul_exp_eq_of_mul_exp_eq_one hε (by ring)

end GlobalTheory.EvenTheta
