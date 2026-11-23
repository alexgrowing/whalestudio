import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfWeightLocPot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentMapContinuousSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralMultipleExtensionStatement
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaCHessComp
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.HessZero

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y ComplexConjugate

theorem matrix_eq_zero_of_quad {e : ℕ} (H : Matrix (Fin e) (Fin e) ℂ)
    (hq : ∀ y : Fin e → ℂ, dotProduct (star y) (Matrix.mulVec H y) = 0) : H = 0 := by
  classical
  have hadd : ∀ a b : Fin e → ℂ, dotProduct (star (a + b)) (Matrix.mulVec H (a + b)) =
      dotProduct (star a) (Matrix.mulVec H a) + dotProduct (star a) (Matrix.mulVec H b) +
      dotProduct (star b) (Matrix.mulVec H a) + dotProduct (star b) (Matrix.mulVec H b) := by
    intro a b
    simp only [star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    ring
  have hsmul : ∀ a b : Fin e → ℂ,
      dotProduct (star (a + Complex.I • b)) (Matrix.mulVec H (a + Complex.I • b)) =
      dotProduct (star a) (Matrix.mulVec H a) + Complex.I * dotProduct (star a) (Matrix.mulVec H b) -
      Complex.I * dotProduct (star b) (Matrix.mulVec H a) + dotProduct (star b) (Matrix.mulVec H b) := by
    intro a b
    simp only [star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, Complex.star_def, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  ext j k
  have e1 := hadd (Pi.single j 1) (Pi.single k 1)
  have e2 := hsmul (Pi.single j 1) (Pi.single k 1)
  rw [hq, hq, hq] at e1 e2
  have hjk : dotProduct (star (Pi.single j (1 : ℂ))) (Matrix.mulVec H (Pi.single k 1)) = H j k := by
    simp [Matrix.mulVec_single, dotProduct_single, Pi.single_apply]
  have hkj : dotProduct (star (Pi.single k (1 : ℂ))) (Matrix.mulVec H (Pi.single j 1)) = H k j := by
    simp [Matrix.mulVec_single, dotProduct_single, Pi.single_apply]
  rw [hjk, hkj] at e1 e2
  rw [Matrix.zero_apply]
  linear_combination (-1/2 : ℂ) * e1 + (Complex.I / 2) * e2 + ((H j k - H k j) / 2) * Complex.I_sq

theorem cHess_comp_eq_zero_of_levi_zero {e : ℕ} (G : (Fin e → ℂ) → ℝ) (τ : ReciprocityTheory.L2DbarEstimates.V e → ReciprocityTheory.L2DbarEstimates.V e)
    {U : Set (ReciprocityTheory.L2DbarEstimates.V e)} {x : ReciprocityTheory.L2DbarEstimates.V e} (hU : IsOpen U) (hx : x ∈ U)
    (hτ : DifferentiableOn ℂ τ U) (hG : ContDiffAt ℝ 2 G ((FinChart.toV e).symm (τ x)))
    (hL : ∀ w, levi G ((FinChart.toV e).symm (τ x)) w = 0) :
    ReciprocityTheory.L2DbarEstimates.cHess e (fun v => ((G ((FinChart.toV e).symm (τ v)) : ℝ) : ℂ)) x = 0 := by
  classical
  set f : ReciprocityTheory.L2DbarEstimates.V e → ℝ := fun u => G ((FinChart.toV e).symm u) with hfdef
  set h : ReciprocityTheory.L2DbarEstimates.V e → ℂ := fun u => ((f u : ℝ) : ℂ) with hhdef
  have hf : ContDiffAt ℝ 2 f (τ x) := hG.comp _ (FinChart.toV e).symm.contDiff.contDiffAt
  have hh : ContDiffAt ℝ 2 h (τ x) := Complex.ofRealCLM.contDiff.contDiffAt.comp _ hf
  have hcomp : (fun v => ((G ((FinChart.toV e).symm (τ v)) : ℝ) : ℂ)) = h ∘ τ := rfl
  rw [hcomp, cmpa_cHess_comp hU hx hτ hh]
  suffices hH0 : cHess e h (τ x) = 0 by rw [hH0]; simp
  have hgc : (fun w => conj (h w)) = h := funext fun w => by simp [h]
  have hH : (cHess e h (τ x)).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show conj (wd e k (wdb e j h) (τ x)) = wd e j (wdb e k h) (τ x)
    have h1 : (fun w => conj (wdb e j h w)) = wd e j h := by
      funext w
      rw [← ChartWirtingerDerivatives.wd_conj' e j h w, hgc]
    rw [← ChartWirtingerDerivatives.wdb_conj' e k (wdb e j h) (τ x), h1, comm_wd_wdb h (τ x) hh j k]
  apply matrix_eq_zero_of_quad
  intro y
  have hre : dotProduct (star y) (Matrix.mulVec (cHess e h (τ x)) y) =
      leviV e h (τ x) (fun k => conj (y k)) := by
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self y
  have hr : (dotProduct (star y) (Matrix.mulVec (cHess e h (τ x)) y)).re = 0 := by
    rw [hre]
    have hz : (FinChart.toV e) ((FinChart.toV e).symm (τ x)) = τ x :=
      (FinChart.toV e).apply_symm_apply _
    have := FinChart.leviV_re_eq_levi (D := e) (h := f) (z := (FinChart.toV e).symm (τ x))
      (by rw [hz]; exact hf) (fun k => conj (y k))
    rw [hz] at this
    rw [this]
    have hfG : f ∘ FinChart.toV e = G := funext fun u => by
      show G ((FinChart.toV e).symm ((FinChart.toV e) u)) = G u
      rw [ContinuousLinearEquiv.symm_apply_apply]
    rw [hfG]
    exact hL _
  exact Complex.ext hr (by simpa using him)

end GlobalTheory.HessZero
