import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anchoredWeight_indefiniteLift_gaps : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
    (p : PtAt ex Csz) (P : ParameterChoice' D L) (i : Fin D.R.m), (i : ℕ) + 1 < D.R.m →
    (dat p i).p + (dat p i).q = D.R.r ∧ GlobalTheory.FlagTan.dimFlag (dat p i) = D.R.f * D.R.r.choose 2 ∧
    ∀ (τ : Psi p.T.Q.H) (k : ℕ), k + 1 < (dat p i).p + (dat p i).q →
      (k + 1 ≠ (dat p i).p → min (LevelStarExponents.gapS D P.Cgap) (LevelStarExponents.h0 L) - 2 ≤ (gap (uW p i τ) k : ℝ)) ∧
      (k + 1 = (dat p i).p → LevelStarExponents.h0 L + D.R.r - 3 ≤ (gap (uW p i τ) k : ℝ)) := by
  first | exact @GlobalTheory.RecGaps.gaps | exact GlobalTheory.RecGaps.gaps | (intros; apply GlobalTheory.RecGaps.gaps <;> assumption)
