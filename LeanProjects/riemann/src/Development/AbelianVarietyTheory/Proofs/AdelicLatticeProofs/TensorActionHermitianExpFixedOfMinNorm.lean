import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebra
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorPowerSumRightActionNormAndContinuity

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.act_exp_eq_of_isMinVec : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (U : Matrix ι ι ℂ) (δ : ι → ℝ), _root_.GlobalTheory.ClassFin.IsMinVec d v → U * Uᴴ = 1 → ∑ i, δ i = 0 → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (δ i) : ℂ)) * Uᴴ)) = _root_.GlobalTheory.ClassFin.nsq v → ∀ s : ℝ, _root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (s * δ i) : ℂ)) * Uᴴ) = v := by
  intro ι _ _ m d v U δ hmin hU hδ hone s
  obtain ⟨act1, actmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  have hUH : Uᴴ * Uᴴᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hU
  have hnormU := (_root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity ι m d).1
  set u := _root_.GlobalTheory.ClassFin.act d v U with hu
  set lam : _root_.GlobalTheory.ClassFin.TIdx ι d → ℝ := fun k => ∑ j, δ (k.2 j) with hlam
  have hdiag : ∀ r : ℝ,
      _root_.GlobalTheory.ClassFin.act d u (diagonal fun i => (Real.exp (r * δ i) : ℂ)) =
        fun k => u k * (Real.exp (r * lam k) : ℂ) := by
    intro r
    funext k
    rw [((_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d u).2.2.1]
    simp only [hlam, Finset.mul_sum, Real.exp_sum, Complex.ofReal_prod]
  have hsplit : ∀ r : ℝ,
      _root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ) =
        _root_.GlobalTheory.ClassFin.act d (fun k => u k * (Real.exp (r * lam k) : ℂ)) Uᴴ := by
    intro r
    rw [actmul, actmul, hdiag]
  have hF : ∀ r : ℝ, _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v
      (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ)) =
        ∑ k, ‖u k‖ ^ 2 * Real.exp (r * lam k) ^ 2 := by
    intro r
    rw [hsplit, hnormU _ _ hUH]
    unfold _root_.GlobalTheory.ClassFin.nsq
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
  have hdet : ∀ r : ℝ, (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ).det = 1 := by
    intro r
    have h1 : U.det * Uᴴ.det = 1 := by rw [← det_mul, hU, det_one]
    rw [det_mul, det_mul, det_diagonal, ← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum,
      hδ, mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one, h1]
  have hmin' : ∀ r : ℝ, _root_.GlobalTheory.ClassFin.nsq v ≤ ∑ k, ‖u k‖ ^ 2 * Real.exp (r * lam k) ^ 2 := by
    intro r
    rw [← hF r]
    exact hmin _ ⟨_, hdet r, rfl⟩
  have h0 : ∑ k, ‖u k‖ ^ 2 * Real.exp (0 * lam k) ^ 2 = _root_.GlobalTheory.ClassFin.nsq v := by
    simp only [zero_mul, Real.exp_zero, one_pow, mul_one]
    exact hnormU v U hU
  have h1 : ∑ k, ‖u k‖ ^ 2 * Real.exp (1 * lam k) ^ 2 = _root_.GlobalTheory.ClassFin.nsq v := by
    rw [← hF 1]
    simpa only [one_mul] using hone
  have hhalf := hmin' (1 / 2)
  have hsq : ∀ k, Real.exp (1 * lam k) ^ 2 = (Real.exp (1 / 2 * lam k) ^ 2) ^ 2 := by
    intro k
    have e : Real.exp (1 * lam k) = Real.exp (1 / 2 * lam k) ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [e]
  have hterm : ∀ k ∈ Finset.univ, 0 ≤ ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 :=
    fun k _ => by positivity
  have hsum : ∑ k, ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 = 0 := by
    have e : ∑ k, ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 =
        ∑ k, ‖u k‖ ^ 2 * Real.exp (1 * lam k) ^ 2 + ∑ k, ‖u k‖ ^ 2 * Real.exp (0 * lam k) ^ 2
          - 2 * ∑ k, ‖u k‖ ^ 2 * Real.exp (1 / 2 * lam k) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsq]
      simp only [zero_mul, Real.exp_zero]
      ring
    refine le_antisymm ?_ (Finset.sum_nonneg hterm)
    rw [e, h0, h1]
    linarith
  have hfix : ∀ k, u k * (Real.exp (s * lam k) : ℂ) = u k := by
    intro k
    have hk := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum k (Finset.mem_univ k)
    rcases mul_eq_zero.mp hk with ha | hb
    · have hz : u k = 0 := by simpa using ha
      simp [hz]
    · have ht : Real.exp (1 / 2 * lam k) ^ 2 = 1 := by
        have := (pow_eq_zero_iff (n := 2) two_ne_zero).mp hb
        linarith
      have hl : lam k = 0 := by
        rw [← Real.exp_nat_mul] at ht
        simpa using (Real.exp_eq_one_iff _).mp ht
      simp [hl]
  rw [hsplit s]
  simp only [hfix]
  rw [← actmul, hU, act1]

end GlobalTheory.ClassFin
