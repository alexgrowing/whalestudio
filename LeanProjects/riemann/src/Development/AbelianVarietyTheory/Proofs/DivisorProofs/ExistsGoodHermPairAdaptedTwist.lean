import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodHermitianLineBundlePair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGenerationAmplePairMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSmallSectionCountRegimeFromRadiusOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftSecondBundleNormPairNormBallGenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairSectionsGoodShiftSecondBundleNormPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallSectionAddMultipleAmpleAfterShiftStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_good_pair_twist : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L N : HermLB p, ∃ (P : Pair p) (b : ℕ) (s t : X.functionField) (c : ℕ),
    P.L = L ∧ P.Good D b s t ∧ GenAt P c ∧ Regime P D ∧ Le ((P.A.pow c).dual) N := by
  intro hAC hHS k _ X _ p D hX L N
  obtain ⟨P₀, b, s, t, hL, hG⟩ := GlobalTheory.VolBr.exists_good_pair hAC k X p D hX L
  obtain ⟨c₀, hc₀, hgen⟩ := GlobalTheory.T.exists_globalGeneration_ample_pair_multiples k X p D hX P₀ hG.ample
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_small_section_add_multiple_ample_after_shift k X p D hX P₀ N s hG.ample hG.s_mem.1 hG.s_ne
  have hc : c₁ ≤ c₀ * (c₁ + 1) := by nlinarith
  have hcpos : 0 < c₀ * (c₁ + 1) := Nat.mul_pos hc₀ (Nat.succ_pos _)
  obtain ⟨u₁, hu₁⟩ := hc₁ (c₀ * (c₁ + 1)) hc hcpos
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.T.exists_shift_smallSectionCount_regime_from_radius_one hAC hHS k X p D hX P₀ hG.ample hG.nef.semiPos
  refine ⟨shiftA P₀ (max 0 (max u₁ u₂)), b, s, t, c₀ * (c₁ + 1), hL, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.hermPairSections_good_shiftSecondBundleNormPair k X p D hX P₀ b s t _ (le_max_left _ _) hG
  · exact (GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation k X p P₀ _).2.2 _ (hgen (c₁ + 1))
  · exact hu₂ _ (le_trans (le_max_right _ _) (le_max_right _ _))
  · exact hu₁ _ (le_trans (le_max_left _ _) (le_max_right _ _))

end GlobalTheory.HSNef
