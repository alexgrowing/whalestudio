import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.AevalMulHomog

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl.EvA

open Red

variable {K : Type} [Field K]

lemma revCol_eq {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : revCol A = A * revCol 1 := by
  ext i j
  first
  | simp [PI.OddDualWeyl.revCol, Matrix.mul_apply, Matrix.one_apply]
  | (rw [Matrix.mul_apply]; simp [PI.OddDualWeyl.revCol, Matrix.one_apply, Finset.sum_ite_eq, Finset.sum_ite_eq'])

lemma det_revCol {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    (revCol A).det = A.det * sgnK K m := by
  rw [revCol_eq A, Matrix.det_mul]
  all_goals rfl

lemma sgn_sq (m : ℕ) : sgnK K m * sgnK K m = 1 := by
  have h : PI.OddDualWeyl.revCol (PI.OddDualWeyl.revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) = 1 := by
    ext i j
    simp only [PI.OddDualWeyl.revCol, Matrix.submatrix_apply]
    rw [Fin.rev_rev]
    all_goals rfl
  have h2 := det_revCol (PI.OddDualWeyl.revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
  rw [h, Matrix.det_one] at h2
  exact h2.symm

lemma arith (x s : K) (hx : x ≠ 0) (hs : s * s = 1) (e e' : ℤ) (D M : ℕ)
    (h : e + e' + (D : ℤ) = (M : ℤ)) (y : K) :
    x ^ e * y = (x⁻¹ * s) ^ e' * (s ^ e' * (x⁻¹ ^ D * (x ^ M * y))) := by
  have hs' : s ^ e' * s ^ e' = 1 := by rw [← _root_.mul_zpow, hs, _root_.one_zpow]
  have key : x ^ e = x⁻¹ ^ e' * (x⁻¹ ^ D * x ^ M) := by
    have h1 : (x⁻¹ ^ D : K) = x ^ (-(D : ℤ)) := by rw [_root_.zpow_neg, _root_.zpow_natCast, _root_.inv_pow]
    have h2 : (x ^ M : K) = x ^ (M : ℤ) := (_root_.zpow_natCast x M).symm
    rw [h1, h2, _root_.inv_zpow', ← _root_.zpow_add₀ hx, ← _root_.zpow_add₀ hx]
    congr 1
    omega
  rw [key, _root_.mul_zpow]
  have h3 : (x⁻¹ ^ e' * s ^ e') * (s ^ e' * (x⁻¹ ^ D * (x ^ M * y))) =
      x⁻¹ ^ e' * (x⁻¹ ^ D * x ^ M) * y * (s ^ e' * s ^ e') := by ring
  rw [h3, hs', _root_.mul_one]

end PI.OddDualWeyl.EvA

namespace PI.OddDualWeyl

open Red EvA

theorem evalDuality : EV := by
  intro K hK m e e' D M F F' h hrel hF' z hz
  have hdz : z.det ≠ 0 := hz.ne_zero
  set ρ : Fin (m + 1) × Fin (m + 1) → K := fun x => z x.1 x.2 with hρ
  have hrel0 : dualSub K (m + 1) F' = (genM K (m + 1)).det ^ M * F := hrel
  have hmap : (MvPolynomial.eval ρ).mapMatrix (genM K (m + 1)) = z := by
    ext i j
    simp [genM, hρ]
  have hgen : MvPolynomial.eval ρ (genM K (m + 1)).det = z.det := by
    rw [RingHom.map_det, hmap]
  have hadj : z.adjugate = z.det • z⁻¹ := by
    calc z.adjugate = z.adjugate * (z * z⁻¹) := by rw [Matrix.mul_nonsing_inv z hz, Matrix.mul_one]
      _ = (z.adjugate * z) * z⁻¹ := by rw [Matrix.mul_assoc]
      _ = z.det • z⁻¹ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hdinv : (z⁻¹).det = z.det⁻¹ := by
    have h1 : z.det * (z⁻¹).det = 1 := by
      rw [← Matrix.det_mul, Matrix.mul_nonsing_inv z hz, Matrix.det_one]
    exact eq_inv_of_mul_eq_one_right h1
  have hdetW : (revCol (z⁻¹)ᵀ).det = z.det⁻¹ * sgnK K m := by
    rw [PI.OddDualWeyl.EvA.det_revCol, Matrix.det_transpose, hdinv]
  have hentry : ∀ i j : Fin (m + 1),
      MvPolynomial.eval ρ (dualM K (m + 1) i j) = z.det * revCol (z⁻¹)ᵀ i j := by
    intro i j
    have h1 : MvPolynomial.eval ρ ((genM K (m + 1)).adjugate (Fin.rev j) i) =
        ((MvPolynomial.eval ρ).mapMatrix (genM K (m + 1))).adjugate (Fin.rev j) i := by
      rw [← RingHom.map_adjugate]
      first
      | rfl
      | simp [RingHom.mapMatrix_apply]
    simp only [dualM, Matrix.of_apply]
    rw [h1, hmap, hadj]
    simp [revCol]
  have hcomp : ∀ (g : Fin (m + 1) × Fin (m + 1) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
      (p : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K),
      MvPolynomial.eval ρ (aeval g p) = MvPolynomial.eval (fun v => MvPolynomial.eval ρ (g v)) p := by
    intro g p
    first
    | (have hh : (MvPolynomial.eval ρ).comp (aeval g).toRingHom =
          MvPolynomial.eval (fun v => MvPolynomial.eval ρ (g v)) := by
         ext <;> simp [MvPolynomial.algebraMap_eq]
       exact RingHom.congr_fun hh p)
    | (induction p using MvPolynomial.induction_on <;> simp_all [MvPolynomial.algebraMap_eq])
  have hscale : ∀ (b : Fin (m + 1) × Fin (m + 1) → K) (c : K),
      MvPolynomial.eval (fun v => c * b v) F' = c ^ D * MvPolynomial.eval b F' := by
    intro b c
    rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdeg : ∑ i, d i = D := by
      have h1 := hF' (MvPolynomial.mem_support_iff.mp hd)
      first
      | (rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1; simpa using h1)
      | simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using h1
      | (rw [← h1]; simp [Finsupp.weight_apply, Finsupp.sum_fintype])
    have hdeg' : ∑ i ∈ d.support, d i = D := by
      rw [← hdeg]
      exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
    have hprod : ∏ i ∈ d.support, (c * b i) ^ d i = c ^ D * ∏ i ∈ d.support, b i ^ d i := by
      rw [← hdeg', ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => _root_.mul_pow _ _ _
    show MvPolynomial.coeff d F' * ∏ i ∈ d.support, (c * b i) ^ d i =
      c ^ D * (MvPolynomial.coeff d F' * ∏ i ∈ d.support, b i ^ d i)
    rw [hprod]
    ring
  have heval : MvPolynomial.eval ρ (dualSub K (m + 1) F') =
      z.det ^ D * MvPolynomial.eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F' := by
    rw [show dualSub K (m + 1) F' =
        aeval (fun v : Fin (m + 1) × Fin (m + 1) => dualM K (m + 1) v.1 v.2) F' from rfl, hcomp]
    rw [show (fun v : Fin (m + 1) × Fin (m + 1) => MvPolynomial.eval ρ (dualM K (m + 1) v.1 v.2)) =
        fun v => z.det * revCol (z⁻¹)ᵀ v.1 v.2 from funext fun v => hentry v.1 v.2]
    exact hscale (fun x => revCol (z⁻¹)ᵀ x.1 x.2) z.det
  have hrel' : z.det ^ D * MvPolynomial.eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F' =
      z.det ^ M * MvPolynomial.eval ρ F := by
    have h1 := congrArg (MvPolynomial.eval ρ) hrel0
    rw [heval, map_mul, map_pow, hgen] at h1
    exact h1
  rw [PI.OddDualWeyl.EvA.arith _ _ hdz (PI.OddDualWeyl.EvA.sgn_sq m) e e' D M h, ← hrel', hdetW,
    MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have h4 : z.det⁻¹ ^ D * (z.det ^ D * MvPolynomial.eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F') =
      MvPolynomial.eval (fun x => revCol (z⁻¹)ᵀ x.1 x.2) F' := by
    rw [← _root_.mul_assoc, ← _root_.mul_pow, inv_mul_cancel₀ hdz, _root_.one_pow, _root_.one_mul]
  rw [h4]

end PI.OddDualWeyl
