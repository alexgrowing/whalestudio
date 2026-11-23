import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StageFunctionNormIntegral
import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_function_norm_integral : ∀ {n : ℕ} {ε : Fin n → Bool} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Subgroup (UJ ε)) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (μ : Measure ↥(KG ε ⊓ M)) [IsProbabilityMeasure μ], (∀ f : Fsp, ‖ι f‖ ^ 2 = ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ) → ∀ {F : UJ ε → U}, Continuous F → (∀ g, restr M F g ∈ Fsp) → ∫ k : KG ε, ‖stageFun M Fsp ι F k‖ ^ 2 ∂muK ε = ∫ k : KG ε, ‖F k‖ ^ 2 ∂muK ε := by
  first | exact @GlobalTheory.RealInd.Stages.stageFun_normSq_integral | exact GlobalTheory.RealInd.Stages.stageFun_normSq_integral | (intros; apply GlobalTheory.RealInd.Stages.stageFun_normSq_integral <;> assumption)
