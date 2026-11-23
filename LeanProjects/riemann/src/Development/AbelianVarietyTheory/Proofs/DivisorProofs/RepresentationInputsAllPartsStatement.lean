import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationInputsAllParts
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representation_inputs_all_parts : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜), AtAll PFire 𝒜 σ ∧ AtAll PRB 𝒜 σ ∧ AtAll PThR 𝒜 σ ∧ AtAll PFrames 𝒜 σ := by
  first | exact @GlobalTheory.Fc.Ind.atAll_fourRows | exact GlobalTheory.Fc.Ind.atAll_fourRows | (intros; apply GlobalTheory.Fc.Ind.atAll_fourRows <;> assumption)
