import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarAct
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdShcSqEqJacPow
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBaseA

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem actR_contDiff {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ContDiff ℝ 1 (actR (ε := ε) g) := by
  open Matrix.Norms.Operator in
  (refine contDiff_iff_contDiffAt.mpr fun z => ?_
   have hf := JacB.contDiffAt_of_exp (𝔸 := Matrix (Fin n) (Fin n) ℂ)
     (f := fun w => (2 : ℝ) • pmat (actR (ε := ε) g w)) (z := z)
     (((JacB.pmat_contDiff ε).continuous.comp (JacB.actR_continuous hg)).const_smul
       (2 : ℝ)).continuousAt
     (by
       refine ContDiffAt.congr_of_eventuallyEq
         ((((contDiff_const (c := gᴴ)).mul (JacB.contDiff_exp_alg.comp
           ((JacB.pmat_contDiff ε).const_smul (2 : ℝ)))).mul
             (contDiff_const (c := g))).contDiffAt)
         (Filter.Eventually.of_forall fun w => ?_)
       exact JacB.exp_two_actR hg w)
     (JacB.fderiv_exp_two_inj _)
   have h2 := (JacB.crdC ε).contDiff.contDiffAt.comp z (hf.const_smul (1 / 2 : ℝ))
   refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
   have e : (1 / 2 : ℝ) • (2 : ℝ) • pmat (actR (ε := ε) g w) = pmat (actR (ε := ε) g w) := by
     rw [smul_smul]
     norm_num
   show actR g w = JacB.crdC ε ((1 / 2 : ℝ) • (2 : ℝ) • pmat (actR (ε := ε) g w))
   rw [e]
   exact (JacB.crd_pmat _).symm)

theorem jacBase {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    |LinearMap.det ((fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 :
      (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))| * Jac y = 1 := by
  set D : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ) :=
    ((fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 :
      (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) with hD
  have hL : LinearMap.det (PolarJacobianDeterminant.shcAdCL y) = Jac y := by
    have h := detP y
    rw [PolarJacobianDeterminant.fderiv_shcAdC] at h
    simpa using h
  have hcomp : (PolarJacobianDeterminant.shcAdCL y).comp D = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    have h1 := JacB.crd_pmat (PolarJacobianDeterminant.shcAdCL y (D v))
    have h2 : shcAd y (pmat (D v)) = pmat v := JacB.shcAd_fderiv_actR y v
    rw [PolarJacobianDeterminant.pmat_shcAdCL, h2, JacB.crd_pmat] at h1
    exact h1.symm
  have hdet : LinearMap.det (PolarJacobianDeterminant.shcAdCL y) * LinearMap.det D = 1 := by
    rw [← LinearMap.det_comp, hcomp, LinearMap.det_id]
  rw [hL] at hdet
  rw [← abs_of_pos (JacB.jac_pos' y), ← abs_mul, mul_comm, hdet, abs_one]

end ReciprocityTheory.ChartRestriction.DS
