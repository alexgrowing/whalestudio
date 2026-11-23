import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsDenseContinuousThetaLawStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionOrthogonalSumApproxFiniteSumsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.DenseSum

theorem unifLimit_prodSpan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), ∀ f, IsThetaFunO ψ S T f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS T) (IsThetaFunO ψ A T) (IsThetaFunO ψ B T)) f := by
  intro D ψ hψ S A B T o f hf ε hε
  obtain ⟨n, P, g, hPc, hPl, hg, hfg⟩ := GlobalTheory.T.theta_function_orthogonal_sum_approx_finite_sums D ψ hψ S A B T o f hf (ε / 2) (by positivity)
  have hb : ∀ i, ∃ C : ℝ, ∀ v, ‖g i v‖ ≤ C := fun i =>
    GlobalTheory.IsoMean.isThetaFunO_bounded B T ψ hψ (g i) (hg i)
  choose C hC using hb
  set M : ℝ := 1 + ∑ i, |C i| with hMdef
  have hM : 0 < M := by
    have : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hδ : 0 < ε / (2 * M) := by positivity
  have hφ : ∀ i, ∃ φ : WO A T → ℂ, IsThetaFunO ψ A T φ ∧ ∀ u, ‖P i u - φ u‖ ≤ ε / (2 * M) := fun i =>
    GlobalTheory.T.theta_functions_dense_continuous_theta_law D ψ hψ A T (P i) (hPc i) (hPl i) _ hδ
  choose φ hφt hφa using hφ
  refine ⟨∑ i, fun w => φ i ((o.resS T) w).1 * g i ((o.resS T) w).2, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨φ i, g i, hφt i, hg i, rfl⟩
  · intro w
    have key : ‖∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2 -
        ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2‖ ≤ ε / 2 := by
      rw [← Finset.sum_sub_distrib]
      calc _ ≤ ∑ i, ‖P i ((o.resS T) w).1 * g i ((o.resS T) w).2 - φ i ((o.resS T) w).1 * g i ((o.resS T) w).2‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i, ε / (2 * M) * |C i| := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [← sub_mul, norm_mul]
            exact mul_le_mul (hφa i _) ((hC i _).trans (le_abs_self _)) (norm_nonneg _) hδ.le
        _ = ε / (2 * M) * ∑ i, |C i| := by rw [Finset.mul_sum]
        _ ≤ ε / (2 * M) * M := by
            refine mul_le_mul_of_nonneg_left ?_ hδ.le
            rw [hMdef]; linarith
        _ = ε / 2 := by field_simp
    have hsum : (∑ i, fun w => φ i ((o.resS T) w).1 * g i ((o.resS T) w).2) w =
        ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2 := by
      simp [Finset.sum_apply]
    rw [hsum]
    calc ‖f w - ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2‖
        = ‖(f w - ∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2) +
          (∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2 - ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2)‖ := by
          congr 1; ring
      _ ≤ ε / 2 + ε / 2 := (norm_add_le _ _).trans (add_le_add (hfg w) key)
      _ = ε := by ring

end GlobalTheory.DenseSum
