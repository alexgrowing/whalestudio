import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaEqualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaBoundRightStatement
import Formalism.LocalRingCardinality.NFLeTwoMulTSq

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem row_hRB_univ : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (Q : V4.Slot) (Lk : LkT Bundle), R1.RankBoundAtBundlePoints Q Lk := by
  intro hDS hHC hRD hCW Q Lk
  refine Row.of_sel fun 𝒜 σ _ _ Fm hc x hx i => ?_
  exact GlobalTheory.T.indefinite_scale_theta_bound_right hRD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B (Fm.parT x hx i).nV_ge
    (GlobalTheory.T.indefinite_scale_theta_equality hDS hHC hRD hCW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B).1

end GlobalTheory.Fc.R1

end
