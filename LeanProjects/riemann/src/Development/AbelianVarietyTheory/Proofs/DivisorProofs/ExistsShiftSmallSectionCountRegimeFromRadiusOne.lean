import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelLargeRadiusPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftSecondBundleNormPairNormBallGenerationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem regime_shiftA : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → P.A.SemiPos D → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Regime (shiftA P u) D := by
  intro hA hHS k _ X _ p D hX P hamp hsemi
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p D hX).2 PUnit fun _ => P.A).1
  have hα := ((hA.arIso k X p D hX).2 PUnit _ Φ hΦ).1 PUnit.unit
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair hHS k X p D hX P 0 1 0 0 P.A _ (Pair.rep_base k X p P).2.1 hamp hsemi hα
  refine ⟨t₀, fun u hu => ⟨Φ (MvPolynomial.X PUnit.unit ^ (D + 1)) / (D + 1).factorial + ((D : ℝ) + 1) * gdeg P.A D / (D + 1).factorial * u, ((D : ℝ) + 1) * gdeg P.A D / (D + 1).factorial, fun t ht => ?_⟩⟩
  have h := ht₀ (t + u) (by linarith)
  have e : ∀ m : ℕ, (shiftA P u).lc 0 m (Real.exp (t * m)) =
      P.lc ((m : ℤ) * 0 + 0) ((m : ℤ) * 1 + 0) (Real.exp ((t + u) * m)) := by
    intro m
    simp only [Pair.lc, (GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation k X p P u).2.1, mul_zero, add_zero, mul_one, ← Real.exp_add]
    congr 4
    push_cast
    ring_nf
  have hfun : (fun m : ℕ => (shiftA P u).lc 0 m (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) =
      fun m : ℕ => P.lc ((m : ℤ) * 0 + 0) ((m : ℤ) * 1 + 0) (Real.exp ((t + u) * m)) / (m : ℝ) ^ (D + 1) :=
    funext fun m => by rw [e]
  rw [hfun]
  convert h using 2
  ring

end GlobalTheory.HSNef
