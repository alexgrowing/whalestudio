import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingEntriesInf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepBoundedEvaluationRows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsOpIntIntegrable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionSmoothL2

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.EvalBound

theorem exists_contRep_bound_of_isKTypeOf : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.I.n → 1 ≤ B.g → ∃ C : ℝ, ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w)) → ∃ f : B.I.GA → ℂ, IsContRep B (A (B.tens B.w)) f ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖A (B.tens B.w)‖ := by
  intro B d hB hL hn hg
  obtain ⟨F, hF, hc, hw⟩ := GlobalTheory.StepAverage.exists_smooth_average_of_isKTypeOf B d hB hL 0 _ (tens_mem_VP B d hB)
  have he := GlobalTheory.StepAverage.isClosedEmbedding_entries_inf B.I
  have hσ : IsURep B.σs := (GlobalTheory.Dec.tensorRep B d hB).1
  obtain ⟨-, -, hN, hC, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  let a : B.I.Ginf → ℂ := fun g => F fun v i j => uMat (g v) i j
  have hs : SmoothInf B.I a := fun x => ⟨F, hF.contDiffAt, Filter.Eventually.of_forall fun _ => rfl⟩
  have hac : HasCompactSupport a := hc.comp_isClosedEmbedding he
  have hai : Integrable a (muInf B.I) := by
    unfold muInf
    exact (hF.continuous.comp he.continuous).integrable_of_hasCompactSupport hac
  obtain ⟨T, hT1, hT2⟩ := GlobalTheory.absOpInt B.I.Ginf (muInf B.I) _ (realRep B) (fun g x => hN _ x)
    (fun x => (hC x).comp (continuous_id.prodMk continuous_const)) a hai
  obtain ⟨C, hC⟩ := GlobalTheory.SmoothGrowth.convolutionSmoothL2 B B.g hn hg a hs hac
  refine ⟨C, fun A hA hk => ?_⟩
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ := hC _ hk T ⟨hai, hT2⟩
  have hfix : T (A (B.tens B.w)) = A (B.tens B.w) := by
    rw [hT1]
    conv_rhs => rw [hw]
    rw [← A.integral_comp_comm (GlobalTheory.StepAverage.integrable_inf B hσ _ hF.continuous hc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have h := congrArg (fun S => S (B.tens B.w)) (hA g)
    simp only [map_smul]
    exact congrArg (a g • ·) h.symm
  rw [hfix] at hf4
  exact ⟨f, ⟨hf2, hf1.1, hf4⟩, hf3⟩

end GlobalTheory.EvalBound
