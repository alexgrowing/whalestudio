import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_GL_norm_one_split : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∃ e : GroundTheory.Automorphic.Reduction.normOneGL E a × ℝ ≃ₜ GA E a, ∀ x t, e (x, t) = splitCentre E a t * (x : GA E a) := by
  first | exact @GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph | exact GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph | (intros; apply GlobalTheory.CompanionTheory.SplitHomeo.exists_homeomorph <;> assumption)
