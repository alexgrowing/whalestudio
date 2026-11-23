import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereMeanEqOfFrameNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.LelongBlocksMulti

theorem log_eval_sub_le_blockSphereMean : ∀ (B N : ℕ) (a : Fin B → ℕ) (A : Matrix (Fin N) (Fin N) ℂ) (h : MvPolynomial (Fin B × Fin N) ℂ), A.det ≠ 0 → IsMultiHomogeneous a h → ∀ p : Fin B × Fin N → ℂ, (∀ i, frameNorm A (fun j => p (i, j)) = 1) → eval p h ≠ 0 → Real.log ‖eval p h‖ - (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2 ≤ blockSphereMean B N (linSubst A h) := by
  intro B N a A h hA hh p hp hne
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rcases Nat.eq_zero_or_pos B with rfl | hB
    · have hev : ∀ z : BlockSphere 0 0, eval (blockPoint z) (linSubst A h) = eval p h := by
        intro z
        rw [GlobalTheory.SphereMeanFrame.eval_linSubst]
        refine congrArg (fun v => eval v h) (funext fun x => ?_)
        exact x.2.elim0
      have hc : (fun z : BlockSphere 0 0 => Real.log ‖eval (blockPoint z) (linSubst A h)‖) =
          fun _ => Real.log ‖eval p h‖ := funext fun z => by rw [hev z]
      unfold blockSphereMean blockSphereProb
      rw [hc, MeasureTheory.Measure.pi_of_empty _ (fun i => i.elim0)]
      simp
    · have := hp ⟨0, hB⟩
      simp [frameNorm] at this
  · let q : Fin B → Fin N → ℂ := fun i => A⁻¹.mulVec (fun j => p (i, j))
    have hq : ∀ i, ‖(WithLp.toLp 2 (q i) : EuclideanSpace ℂ (Fin N))‖ = 1 := by
      intro i
      rw [EuclideanSpace.norm_eq]
      exact hp i
    let u : BlockSphere B N := fun i =>
      ⟨WithLp.toLp 2 (q i), mem_sphere_zero_iff_norm.mpr (hq i)⟩
    have hev : eval (blockPoint u) (linSubst A h) = eval p h := by
      rw [GlobalTheory.SphereMeanFrame.eval_linSubst]
      refine congrArg (fun v => eval v h) (funext fun x => ?_)
      obtain ⟨b, j⟩ := x
      have h1 : A.mulVec (q b) = fun j => p (b, j) := by
        simp only [q]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.one_mulVec]
      exact congrFun h1 j
    have key := blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable hN B
      a (linSubst A h) u (GlobalTheory.HeightUnique.linSubst_homog A hh) (by rw [hev]; exact hne)
    rw [hev] at key
    calc Real.log ‖eval p h‖ - (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2
        = Real.log ‖eval p h‖ - (∑ i, (a i : ℝ)) / 2 * (harmonic (N - 1) : ℝ) := by ring
      _ ≤ _ := by push_cast at key ⊢; exact key

end GlobalTheory.LelongBlocksMulti
