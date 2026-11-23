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
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.AnForm.A

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def tailCL (d : ℕ) : (Fin (d + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

theorem tailCL_coe (d : ℕ) : (⇑(tailCL d) : (Fin (d + 1) → ℂ) → (Fin d → ℂ)) = Fin.tail := by
  funext z i
  rfl

theorem jacC_tailCL (d : ℕ) (z : Fin (d + 1) → ℂ) (a : Fin d) (k : Fin (d + 1)) :
    jacC (⇑(tailCL d)) z a k = if a.succ = k then 1 else 0 := by
  have h := ContinuousLinearMap.fderiv (𝕜 := ℂ) (x := z) (tailCL d)
  simp only [jacC, h]
  simp [tailCL, Pi.single_apply, eq_comm]

theorem hessC_comp_tail (d : ℕ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p : ℂ)
    (hα : ContDiffAt ℝ 2 α y) :
    hessC (fun z : Fin (d + 1) → ℂ => α (Fin.tail z)) (Fin.cons p y) = blk 0 (hessC α y) := by
  have ht : (tailCL d) (Fin.cons p y : Fin (d + 1) → ℂ) = y := by
    rw [tailCL_coe]; exact Fin.tail_cons _ _
  have h := hessC_comp α (⇑(tailCL d)) (Fin.cons p y : Fin (d + 1) → ℂ)
    ((tailCL d).analyticAt _) (by rw [ht]; exact hα)
  have hfun : α ∘ ⇑(tailCL d) = fun z : Fin (d + 1) → ℂ => α (Fin.tail z) := by
    rw [tailCL_coe]; rfl
  rw [hfun, ht] at h
  rw [h]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  all_goals
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, jacC_tailCL, blk,
      Fin.succ_ne_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem hessC_row_fibre : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p e : ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (s v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p y) → ContDiffAt ℝ 2 α y → hessC f (Fin.cons p y) = blk e B →
    hessC (fun z : Fin (d + 1) → ℂ => s * f z + v * α (Fin.tail z)) (Fin.cons p y) =
    blk ((s : ℂ) * e) ((s : ℂ) • B + (v : ℂ) • hessC α y) := by
  intro d f α y p e B s v hf hα hB
  have ht : (Fin.tail (Fin.cons p y : Fin (d + 1) → ℂ) : Fin d → ℂ) = y := Fin.tail_cons _ _
  have htail : ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => α (Fin.tail z))
      (Fin.cons p y : Fin (d + 1) → ℂ) := by
    have hα' : ContDiffAt ℝ 2 α ((tailCL d) (Fin.cons p y : Fin (d + 1) → ℂ)) := by
      rw [tailCL_coe, ht]; exact hα
    have hl : ContDiffAt ℝ 2 (⇑((tailCL d).restrictScalars ℝ))
        (Fin.cons p y : Fin (d + 1) → ℂ) := ((tailCL d).restrictScalars ℝ).contDiff.contDiffAt
    have := ContDiffAt.comp (g := α) (f := ⇑((tailCL d).restrictScalars ℝ))
      (Fin.cons p y : Fin (d + 1) → ℂ) hα' hl
    have hfun : α ∘ ⇑((tailCL d).restrictScalars ℝ) = fun z : Fin (d + 1) → ℂ => α (Fin.tail z) := by
      funext z
      simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [tailCL_coe]
    rwa [hfun] at this
  rw [ReciprocityTheory.AnForm.M.hessC_add' (fun z => s * f z) (fun z => v * α (Fin.tail z)) _
    (contDiffAt_const.mul hf) (contDiffAt_const.mul htail),
    ReciprocityTheory.AnForm.M.hessC_const_mul' s f, ReciprocityTheory.AnForm.M.hessC_const_mul' v (fun z => α (Fin.tail z)), hB, hessC_comp_tail d α y p hα]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [blk]

end GlobalTheory.CompanionTheory.Ar.PB.FibN
