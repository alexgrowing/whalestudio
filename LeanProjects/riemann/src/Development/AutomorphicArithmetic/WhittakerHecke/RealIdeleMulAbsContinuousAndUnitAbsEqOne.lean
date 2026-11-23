import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleModuleInfId
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private noncomputable def cu (y : ℝ) (h : y ≠ 0) : (TR.Rinf ℚ)ˣ :=
  ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ h, funext fun _ => inv_mul_cancel₀ h⟩

private theorem iy_eq {y : ℝ} (h : y ≠ 0) : iy y = TR.infId ℚ (cu y h) := dif_neg h

private theorem nrm_unit {v : H.P ℚ} {x : H.Kv v} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one :
    (∀ y y' : ℝ, y ≠ 0 → y' ≠ 0 → iy (y * y') = iy y * iy y') ∧ (∀ y : ℝ, y ≠ 0 → ab (iy y) = |y|) ∧ Continuous (fun t : ℝ => iy (Real.exp t)) ∧ ∀ u ∈ UU, ab u = 1 := by
  refine ⟨fun y y' hy hy' => ?_, fun y hy => ?_, ?_, fun u hu => ?_⟩
  · rw [iy_eq (mul_ne_zero hy hy'), iy_eq hy, iy_eq hy', ← map_mul]
    congr 1
    exact Units.ext rfl
  · rw [iy_eq hy]
    show (IdeleGroup.ideleModule ℚ (TR.infId ℚ (cu y hy)) : ℝ) = |y|
    rw [GlobalTheory.HenQ.DetSplit.ideleModule_infId]
    simp [cu]
  · have hu : Continuous fun t : ℝ => cu (Real.exp t) (Real.exp_ne_zero t) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · exact continuous_pi fun _ => Real.continuous_exp
      · exact continuous_pi fun _ => Real.continuous_exp.inv₀ Real.exp_ne_zero
    have he : (fun t : ℝ => iy (Real.exp t)) = fun t => TR.infId ℚ (cu (Real.exp t) (Real.exp_ne_zero t)) :=
      funext fun t => iy_eq (Real.exp_ne_zero t)
    rw [he]
    exact (TR.continuous_infId ℚ).comp hu
  · show (IdeleGroup.ideleModule ℚ u : ℝ) = 1
    rw [IdeleGroup.ideleModule_eq]
    have h1 : ((u : A ℚ)).1 = 1 := hu.1
    have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖((u : A ℚ)).2 v‖ = 1 :=
      finprod_eq_one_of_forall_eq_one fun v => nrm_unit (hu.2 v)
    rw [h1, h2, mul_one]
    exact Finset.prod_eq_one fun w _ => by
      rw [show (1 : InfiniteAdeleRing ℚ) w = 1 from rfl, norm_one, one_pow]
