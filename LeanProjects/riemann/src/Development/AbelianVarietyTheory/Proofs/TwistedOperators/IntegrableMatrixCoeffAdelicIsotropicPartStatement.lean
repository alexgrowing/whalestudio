import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffAdelicIsotropicPart
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_matrixCoeff_adelicIsotropicPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → Integrable (fun y : Mx D W.rank r => ∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y)) F w * star (G w) ∂μV) μ := by
  first | exact @GlobalTheory.CoefInteg.integrable_coef | exact GlobalTheory.CoefInteg.integrable_coef | (intros; apply GlobalTheory.CoefInteg.integrable_coef <;> assumption)
