import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem ex_prod' {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Wt n) :
    ∏ a ∈ s, ex (f a) = ex (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [(cfBasic n).2.1]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, (cfBasic n).1]

private theorem ex_pow' {n : ℕ} (x : Wt n) (k : ℕ) : ex x ^ k = ex (k • x) := by
  induction k with
  | zero => simp [(cfBasic n).2.1]
  | succ k ih => rw [pow_succ, ih, ← (cfBasic n).1, succ_nsmul]

private theorem sg_smul' {n : ℕ} (w : Equiv.Perm (Fin n)) (f : FR n) :
    sg w • f = (((Equiv.Perm.sign w : ℤ) : FR n)) * f := by
  rw [sg, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

theorem UpperTheory.RealTr.denom :
    ∀ (n : ℕ) (t : ℝ), alt (t • rhoV n) = ex (t • rhoV n) * ∏ p ∈ posP n, (1 - ex (-(t • rt p.1 p.2))) := by
  intro n t
  classical
  set Y : Fin n → FR n := fun a => ex (-(t • (Pi.single a (1 : ℝ) : Wt n))) with hY
  set c : Wt n := fun _ => t * (((n : ℝ) - 1) / 2) with hc
  have hA : alt (t • rhoV n) = ex c * (Matrix.vandermonde Y).transpose.det := by
    rw [Matrix.det_apply, Finset.mul_sum, alt]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hprod : ex c * ∏ i, (Matrix.vandermonde Y).transpose (w i) i = ex ((t • rhoV n) ∘ ⇑w) := by
      simp only [Matrix.transpose_apply, Matrix.vandermonde_apply, hY, ex_pow', ex_prod',
        ← (cfBasic n).1]
      congr 1
      funext b
      simp [Finset.sum_apply, Pi.single_apply, rhoV]
      ring
    rw [mul_smul_comm, hprod, sg_smul', Units.smul_def, zsmul_eq_mul]
  have h1 : ∀ a b : Fin n, 1 - ex (-(t • rt a b)) = ex (t • (Pi.single b (1 : ℝ) : Wt n)) * (Y b - Y a) := by
    intro a b
    rw [mul_sub, hY]
    simp only
    rw [← (cfBasic n).1, ← (cfBasic n).1, add_neg_cancel, (cfBasic n).2.1]
    congr 2
    rw [rt, smul_sub]
    abel
  have h2 : ∏ p ∈ posP n, (1 - ex (-(t • rt p.1 p.2))) =
      ∏ i, ∏ j ∈ Finset.Ioi i, (1 - ex (-(t • rt i j))) := by
    unfold posP
    rw [Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  have h3 : ex (t • rhoV n) * ∏ i, ∏ j ∈ Finset.Ioi i, ex (t • (Pi.single j (1 : ℝ) : Wt n)) = ex c := by
    simp only [ex_prod', ← (cfBasic n).1]
    congr 1
    funext k
    simp [Finset.sum_apply, Pi.single_apply, rhoV]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
      Fin.card_Iio, nsmul_eq_mul, hc]
    ring
  rw [h2, hA, Matrix.det_transpose, Matrix.det_vandermonde, ← h3]
  simp_rw [h1, Finset.prod_mul_distrib]
  ring
