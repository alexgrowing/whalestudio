import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentImageDegreeBetweenOfProportionalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPrincipalisationBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualVolumeDeepLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProportionalPositiveVolumesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMultiplicityWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.CovTop.DegProof

set_option maxHeartbeats 1000000 in

theorem deg : HypothesesX → Hypotheses2 → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation →
    GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg := by
  intro hX h2 hS hT hG hQ hN hDG hSz hF
  have hP := GlobalTheory.T.stronger_published_hypotheses_imply h2
  refine Closed.imp (Closed.and (Closed.and (GlobalTheory.T.valuation_multiplicity_weight h2 hG hQ hS hT hN hDG hSz hF) wtBig_run)
    (Closed.and (Closed.and (GlobalTheory.T.weight_parameter_strict_antitone hSz) (GlobalTheory.T.size_bounds_for_family hSz)) hDG)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, -, a₁⟩, _, -, a₂⟩, ⟨⟨_, -, a₃⟩, _, -, a₄⟩, _, -, a₅⟩
  obtain ⟨x0, a⟩ := (a₁.and a₂).and ((a₃.and a₄).and a₅)
  clear a₁ a₂ a₃ a₄ a₅
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨a₁, a₂⟩, ⟨a₃, a₄⟩, a₅⟩ := a x hx hle ι p hp
  clear a
  obtain ⟨hp1, hq1, hE, hQuo, hAnti, -, -⟩ := a₃ i hi
  obtain ⟨hLaw, hIn, -⟩ := a₄ i hi Y hY
  obtain ⟨-, -, -, -, -, -, ⟨Z'⟩, -⟩ := a₅ i hi Y hY
  have hW := a₂ i hi
  have hV := a₁ i hi Y hY
  rw [hQuo u1 hu1]
  have hPr := GlobalTheory.T.proportional_positive_volumes h2 hS hT hN _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1
  have hEq := GlobalTheory.T.equal_volume_deep_level h2 hS hT hN _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1
  have hBir := GlobalTheory.T.weight_principalisation_bound hX hG hQ hS hP h2.q15 h2.q16 _ p.T hLaw _ hp1 hq1 Y _ _ hY.1 _ (fun τ a b hab => by
    have hb := b.2
    have h := hW.gaps τ a (by rw [← hab]; exact hb)
    rw [gap_eq _ hab] at h
    refine le_trans ?_ h
    have e : ∀ d C N : ℕ, (d + 3) ^ 2 + 2 * N ≤ (d + 3) * (C + 4 * N + d + 3) := fun d C N => by nlinarith
    rw [GlobalTheory.CompHS.dimFlag_eq]
    exact_mod_cast e _ _ _)
  have key := GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.1.unf hPr.1 hEq _ (fun τ => (hAnti τ).1) (fun τ => (hAnti τ).2) hBir hV
  refine ⟨CompHt.delPrime Y.U Z' _, ?_, fun Z => key Z Z'⟩
  exact mul_pos (hPr.2 Z') (Int.cast_pos.2 (CompHt.vdm_pos fun τ => (hAnti τ).2))

end GlobalTheory.CovTop.DegProof
