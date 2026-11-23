import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralRealUnitaryHaarEqProdUpqHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_realUnitary_haar_eq_prod_Upq_haar : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (mR : Measure (GinfC V)) (μ : ∀ τ, Measure (Formalism.REAL.UJ (M.ε τ))), mR.IsHaarMeasure → (∀ τ, (μ τ).IsHaarMeasure) → ∃ c : ℝ, 0 < c ∧ ∀ F : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ, (∀ τ, Integrable (fun u : Formalism.REAL.UJ (M.ε τ) => F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u))) (μ τ)) → Integrable (fun g : GinfC V => ∏ τ, F τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) (g : GA D V))) mR ∧ ∫ g : GinfC V, ∏ τ, F τ (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) (g : GA D V)) ∂mR = (c : ℂ) * ∏ τ, ∫ u : Formalism.REAL.UJ (M.ε τ), F τ (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ofFr M τ (umat u)) ∂μ τ := by
  first | exact @GlobalTheory.HaarReal.integral_prod_eq | exact GlobalTheory.HaarReal.integral_prod_eq | (intros; apply GlobalTheory.HaarReal.integral_prod_eq <;> assumption)
