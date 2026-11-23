import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaEqualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaBoundRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaIdentityStatement
import Formalism.LocalRingCardinality.NFLeTwoMulTSq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem atAll_fourRows : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜),
      AtAll PFire 𝒜 σ ∧ AtAll PRB 𝒜 σ ∧ AtAll PThR 𝒜 σ ∧ AtAll PFrames 𝒜 σ := by
  intro hDS hHC hRD hCW 𝒜 σ
  have hF : AtAll PFire 𝒜 σ := fun Fm hc x hx i =>
    GlobalTheory.T.indefinite_scale_theta_equality hDS hHC hRD hCW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B
  refine ⟨hF, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_⟩
  · exact GlobalTheory.T.indefinite_scale_theta_bound_right hRD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B (Fm.parT x hx i).nV_ge (hF Fm hc x hx i).1
  · exact GlobalTheory.T.indefinite_scale_theta_identity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).Rr (hF Fm hc x hx i).1
  · exact GlobalTheory.T.indefinite_scale_theta_sum _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).pins

end GlobalTheory.Fc.Ind

end
