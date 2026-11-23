import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_translate_atRealPlace : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), IsAutFunSm θ V (rTr V (atTau θ V τ g) φ) := by
  first | exact @GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau | exact GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau | (intros; apply GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau <;> assumption)
