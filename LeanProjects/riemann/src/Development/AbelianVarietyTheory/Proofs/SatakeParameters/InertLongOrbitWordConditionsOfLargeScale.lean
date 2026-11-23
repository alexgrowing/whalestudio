import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElevenLeInertOddPrimeImagQuadraticLargeScale
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PageLargeScaleBoundsOfLargeScale
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qdStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLongOrbitSmallPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersLetterwiseStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsCommonNaturalRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThickLetterWordHypothesesOfCommonConditionsStatement

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem jointB_of_large : ∀ eps ez C₂ A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L)
    (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D →
    (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointB L HW C₂ := by
  intro eps ez C₂ A heps hez
  obtain ⟨x1, h1⟩ := GlobalTheory.HTW.roomy_of_large eps (max 100 (2 * C₂)) A heps (le_max_left _ _)
  obtain ⟨x2, h2⟩ := GlobalTheory.InertPrimeEleven.eleven_le ez hez
  refine ⟨max x1 x2, ?_⟩
  intro D L Pm HW hE hZ hA hx hadm hfont hJ i hin hrow r ρ π hPt w hw
  have hR : Roomy L (max 100 (2 * C₂)) := h1 D L Pm hE hA (le_trans (le_max_left _ _) hx)
  have h11 : 11 ≤ D.nd.l i :=
    h2 D L (D.nd.l i) hZ (le_trans (le_max_right _ _) hx) Fact.out hin
  refine ⟨GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw hin.1 hin.2.1 hin.2.2.1, ?_⟩
  intro Cx hG
  obtain ⟨ε, g, hg, hB⟩ := GlobalTheory.T.wordConditions_common_natural_representation L _ HW i r ρ π w hw Cx hG hR hadm hfont hJ hPt hin.1 hin.2.1 hin.2.2.1
  have hWB : WordsB L (D.nd.l i) C₂ (recWord L (liftIdx D i) ε g) := by
    refine GlobalTheory.T.twistedDualSizeWord_long_orbit_small_prime L Pm _ C₂ _ ε g _ (D.nd.l i) hR hg (le_max_right _ _) h11 hrow.1 ?_
    rw [Prod.snd_inv, orderOf_inv]
    exact hrow.lt_orderOf
  refine ⟨_, hB, GlobalTheory.T.thickLetterWord_hypotheses_of_common_conditions L HW i r ρ π w hw Cx hG _ hin.ne_two hB, h11, hWB.j_lt, hWB.par, ?_⟩
  intro t ht
  exact GlobalTheory.T.cyclicWordMarkedClusters_letterwise _ _ hWB.clusters t ht

end GlobalTheory.HTW.RecS
