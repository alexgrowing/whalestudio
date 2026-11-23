import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLogNcardSeminormBallOneGe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelLargeRadiusPairStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_one_eventually_ge : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → M.IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a + a') (m * b + b') 1 := by
  intro hA k _ X _ p D hD P a b a' b' M α hRep hAmp hSP hSI ε hε
  obtain ⟨t₀, ht⟩ := GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair hA k X p D hD P a b a' b' M α hRep hAmp hSP hSI
  exact GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge X.functionField
    (fun m : ℕ => P.H (m * a + a') (m * b + b')) (fun m : ℕ => P.Bl (m * a + a') (m * b + b')) (D + 1)
    (Nat.succ_pos D) (fun m => GlobalTheory.VolBr.Pair.isBallFam k X p P _ _)
    (fun m R => GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hD P _ _ R) _ _ t₀ ht ε hε

end GlobalTheory.HSNef
