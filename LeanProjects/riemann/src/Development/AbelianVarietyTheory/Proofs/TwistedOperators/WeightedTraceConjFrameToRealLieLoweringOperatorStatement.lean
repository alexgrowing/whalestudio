import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedTraceConjFrameToRealLieLoweringOperator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedTrace_conjFrameToRealLie_loweringOperator : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ (m : D.what₂.Tau → ℤ) (ρ : D.what₂.Tau) (c d : Fin T.rank), c < d → ∀ (Z Z' : Frame C.X.Ψ T.rank), Z ∈ GlobalTheory.HolRead.unitLie C.X → Z' ∈ GlobalTheory.HolRead.unitLie C.X → Z + I • Z' = GlobalTheory.HolRead.unitFr (C.m.e ρ) c d → GlobalTheory.AdSpan.ConjHol.trLin T m (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z) + I * GlobalTheory.AdSpan.ConjHol.trLin T m (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z') = 0 := by
  first | exact @GlobalTheory.AdSpan.ConjHol.trLin_toLieC_unitFr | exact GlobalTheory.AdSpan.ConjHol.trLin_toLieC_unitFr | (intros; apply GlobalTheory.AdSpan.ConjHol.trLin_toLieC_unitFr <;> assumption)
