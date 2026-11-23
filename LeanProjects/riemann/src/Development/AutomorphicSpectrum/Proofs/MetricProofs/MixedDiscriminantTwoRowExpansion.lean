import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem derivation_prod_erase_xt {σ ι : Type*} [DecidableEq ι]
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) (a : ι → MvPolynomial σ ℝ) (S : Finset ι) :
    D (∏ i ∈ S, a i) = ∑ i ∈ S, D (a i) * ∏ j ∈ S.erase i, a j := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, D.leibniz, ih, Finset.sum_insert hi, Finset.erase_insert hi,
      smul_eq_mul, smul_eq_mul, add_comm, mul_comm (∏ j ∈ S, a j), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Finset.erase_insert_of_ne hij,
      Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h))]
    ring

theorem derivation_prod_succAbove_xt {σ : Type*} {n : ℕ}
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) (a : Fin (n + 1) → MvPolynomial σ ℝ) :
    D (∏ r, a r) = ∑ r, D (a r) * ∏ s, a (r.succAbove s) := by
  rw [derivation_prod_erase_xt]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  rw [Fin.univ_succAbove _ r, Finset.cons_eq_insert, Finset.erase_insert (by simp), Finset.prod_map]
  rfl

theorem pderiv_rowW_zero_xt (u : Fin 2 → ℝ) (v : ℝ) : pderiv (some 0) (rowW u v) = C (u 0) := by
  simp [rowW, pderiv_X, Pi.single_apply, pderiv_C, Derivation.leibniz]

theorem pderiv_rowW_one_xt (u : Fin 2 → ℝ) (v : ℝ) : pderiv (some 1) (rowW u v) = C (u 1) := by
  simp [rowW, pderiv_X, Pi.single_apply, pderiv_C, Derivation.leibniz]

theorem pderiv_C_mul_xt {σ : Type*} [DecidableEq σ] (j : σ) (a : ℝ) (p : MvPolynomial σ ℝ) :
    pderiv j (C a * p) = C a * pderiv j p := by
  simp [Derivation.leibniz, pderiv_C]

theorem linear_form_linear_combination (a b : ℝ) (n m : Fin 3 → ℝ) :
    lin4 (fun i => a * n i + b * m i) = C a * lin4 n + C b * lin4 m := by
  simp only [lin4, lin3, map_sum, map_mul, rename_X, rename_C, Finset.mul_sum,
    ← Finset.sum_add_distrib, map_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem evalW_C_xt (n₀ n₁ : Fin 3 → ℝ) (a : ℝ) : evalW n₀ n₁ (C a) = C a := by
  simp [evalW]

theorem evalW_rowW_xt (n₀ n₁ : Fin 3 → ℝ) (u : Fin 2 → ℝ) (v : ℝ) :
    evalW n₀ n₁ (rowW u v) = lin4 (fun i => u 0 * n₀ i + u 1 * n₁ i) + C v * X none := by
  rw [linear_form_linear_combination]
  simp [evalW, rowW]

theorem mdisc_extract_two : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (u : Fin (d + 2) → Fin 2 → ℝ) (v : Fin (d + 2) → ℝ) (n₀ n₁ : Fin 3 → ℝ) (e₀ e₁ : ℂ),
      ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁)
        ((∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))) =
      e₀ * e₁ * L (evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))))) := by
  intro d T H L hL u v n₀ n₁ e₀ e₁
  have hLC : ∀ (a : ℝ) (p : MvPolynomial (Option (Fin 3)) ℝ), L (C a * p) = (a : ℂ) * L p := by
    intro a p
    rw [← smul_eq_C_mul, map_smul, Complex.real_smul]
  let M : Fin (d + 2) → Matrix (Fin d) (Fin d) ℂ := fun r =>
    (∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H
  have h1 : ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁) (M r))) =
      ∑ r, ((u r 0 : ℂ) * e₀) * (((d + 1).factorial : ℂ) *
        mdisc fun s => blk ((u (r.succAbove s) 1 : ℂ) * e₁) (M (r.succAbove s))) :=
    (GlobalTheory.T.mixed_discriminant_cofactor_expansion (d + 1)).1 (fun r => (u r 0 : ℂ) * e₀) (fun r => blk ((u r 1 : ℂ) * e₁) (M r))
  have h2 : ∀ r : Fin (d + 2), ((d + 1).factorial : ℂ) *
      mdisc (fun s => blk ((u (r.succAbove s) 1 : ℂ) * e₁) (M (r.succAbove s))) =
      ∑ s, ((u (r.succAbove s) 1 : ℂ) * e₁) * ((d.factorial : ℂ) *
        mdisc fun t => M (r.succAbove (s.succAbove t))) := fun r =>
    (GlobalTheory.T.mixed_discriminant_cofactor_expansion d).1 (fun s => (u (r.succAbove s) 1 : ℂ) * e₁) (fun s => M (r.succAbove s))
  have h3 : ∀ (r : Fin (d + 2)) (s : Fin (d + 1)),
      (d.factorial : ℂ) * mdisc (fun t => M (r.succAbove (s.succAbove t))) =
      L (∏ t, evalW n₀ n₁ (rowW (u (r.succAbove (s.succAbove t))) (v (r.succAbove (s.succAbove t))))) := by
    intro r s
    simp only [evalW_rowW_xt]
    exact hL (fun t i => u (r.succAbove (s.succAbove t)) 0 * n₀ i + u (r.succAbove (s.succAbove t)) 1 * n₁ i)
      (fun t => v (r.succAbove (s.succAbove t)))
  have h4 : pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))) =
      ∑ r, C (u r 0) * ∑ s, C (u (r.succAbove s) 1) *
        ∏ t, rowW (u (r.succAbove (s.succAbove t))) (v (r.succAbove (s.succAbove t))) := by
    rw [derivation_prod_succAbove_xt]
    simp only [pderiv_rowW_zero_xt, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pderiv_C_mul_xt, derivation_prod_succAbove_xt]
    simp only [pderiv_rowW_one_xt]
  show ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁) (M r))) = _
  rw [h1, h4]
  simp only [h2, h3, map_sum, map_mul, map_prod, evalW_C_xt, hLC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
