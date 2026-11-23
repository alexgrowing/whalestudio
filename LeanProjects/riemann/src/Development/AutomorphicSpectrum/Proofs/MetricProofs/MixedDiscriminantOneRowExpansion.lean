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

theorem pderiv_fin_prod {σ : Type*} (k : σ) : ∀ (d : ℕ) (f : Fin (d + 1) → MvPolynomial σ ℝ),
    pderiv k (∏ r, f r) = ∑ r, pderiv k (f r) * ∏ s, f (r.succAbove s) := by
  intro d
  induction d with
  | zero => intro f; simp
  | succ d ih =>
    intro f
    rw [Fin.prod_univ_succ, Derivation.leibniz, ih (fun i => f i.succ),
      Fin.sum_univ_succ (fun r => pderiv k (f r) * ∏ s, f (r.succAbove s))]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · simp only [Fin.succAbove_zero]
      ring
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [Fin.prod_univ_succ (fun s => f (r.succ.succAbove s))]
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
      ring

theorem pderiv_row_weight (c v : ℝ) : pderiv (some 0 : Option (Fin 2)) (rowW ![c, 0] v) = C c := by
  simp [rowW, pderiv_X, Pi.single_apply]

theorem eval_row_weight (n : Fin 3 → ℝ) (c v : ℝ) :
    evalW n n (rowW ![c, 0] v) = lin4 (fun i => c * n i) + C v * X none := by
  have h : lin4 (fun i => c * n i) = C c * lin4 n := by
    simp only [lin4, lin3, map_sum, map_mul, rename_C, rename_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]
  simp [rowW, evalW, aeval_def, algebraMap_eq]

theorem extract_one : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (c : Fin (d + 1) → ℝ) (v : Fin (d + 1) → ℝ) (n : Fin 3 → ℝ) (e : ℂ),
      ((d + 1).factorial : ℂ) * mdisc (fun r => blk ((c r : ℂ) * e)
        ((∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H)) =
      e * L (evalW n n (pderiv (some 0) (∏ r, rowW ![c r, 0] (v r)))) := by
  intro d T H L hL c v n e
  have h1 := ((GlobalTheory.T.mixed_discriminant_cofactor_expansion d).1 (fun r => (c r : ℂ) * e)
    (fun r => (∑ i, ((c r * n i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))
  refine h1.trans ?_
  rw [pderiv_fin_prod, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h3 := hL (fun s i => c (r.succAbove s) * n i) (fun s => v (r.succAbove s))
  rw [h3, pderiv_row_weight, map_mul (evalW n n), map_prod (evalW n n)]
  simp only [eval_row_weight]
  have h4 : evalW n n (C (c r)) = C (c r) := by simp [evalW, aeval_def, algebraMap_eq]
  rw [h4, C_mul', map_smul, Complex.real_smul]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
