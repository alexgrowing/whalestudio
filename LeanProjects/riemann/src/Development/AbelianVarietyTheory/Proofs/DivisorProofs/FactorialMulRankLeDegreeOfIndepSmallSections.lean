import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelLargeRadiusPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeminormBallFamilyPowLeEncardOfLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeOfGrowthInRadiusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBallFamMonoNegAdd
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.factorial_mul_le_gdeg_of_indep : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (M : HermLB p), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → ∀ (ρ : ℕ) (t₁ : ℝ), (∀ m : ℕ, 0 < m → ∃ v : Fin (ρ * m ^ D) → X.functionField, LinearIndependent ℤ v ∧ ∀ s, v s ∈ P.Bl (m * a) (m * b) (Real.exp (t₁ * m))) → (D.factorial : ℝ) * ρ ≤ gdeg M D := by
  intro hA hHS k _ X _ p D hX P a b M hRep hAmp hSemi ρ t₁ hv
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p D hX).2 PUnit fun _ => M).1
  have hα : M.IsSelfInter (Φ (MvPolynomial.X PUnit.unit ^ (D + 1))) :=
    ((hA.arIso k X p D hX).2 PUnit _ Φ hΦ).1 PUnit.unit
  obtain ⟨t₀, hlim⟩ := GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair hHS k X p D hX P a b 0 0 M _ hRep hAmp hSemi hα
  have key := GlobalTheory.T.le_slope_of_tendsto_div_pow_of_log_lower_bound D (fun t m => P.lc (m * a) (m * b) (Real.exp (t * m)))
    (Φ (MvPolynomial.X PUnit.unit ^ (D + 1)) / ((D + 1).factorial : ℝ))
    (((D : ℝ) + 1) * gdeg M D / ((D + 1).factorial : ℝ)) ρ t₀ t₁ (Nat.cast_nonneg _) ?_ ?_
  · have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * (D.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
    have hD1 : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    rw [hf, mul_div_mul_left _ _ hD1.ne', le_div_iff₀ hD] at key
    linarith
  · intro t ht
    simpa using hlim t ht
  · intro t m Q hm hQ hle
    obtain ⟨v, hli, hvB⟩ := hv m hm
    have hB := GlobalTheory.VolBr.Pair.isBallFam k X p P (m * a) (m * b)
    have hcard := GlobalTheory.T.seminormBallFamily_pow_le_encard_of_linearIndependent _ _ _ hB (ρ * m ^ D) Q (Real.exp (t₁ * m)) v (Real.exp_pos _).le hli hvB
    have hsub : P.Bl (m * a) (m * b) (((ρ * m ^ D : ℕ) : ℝ) * Q * Real.exp (t₁ * m)) ⊆
        P.Bl (m * a) (m * b) (Real.exp (t * m)) :=
      (GlobalTheory.VolBr.isBallFam_mono_neg_add _ _ _ hB).1 _ _ (by push_cast; linarith)
    have hfin := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P (m * a) (m * b) (Real.exp (t * m))
    have h1 : ((Q ^ (ρ * m ^ D) : ℕ) : ℕ∞) ≤ (P.Bl (m * a) (m * b) (Real.exp (t * m))).encard :=
      hcard.trans (Set.encard_le_encard hsub)
    rw [← hfin.cast_ncard_eq] at h1
    have hn : Q ^ (ρ * m ^ D) ≤ (P.Bl (m * a) (m * b) (Real.exp (t * m))).ncard := by exact_mod_cast h1
    show _ ≤ Real.log _
    have hQ' : (0 : ℝ) < ((Q ^ (ρ * m ^ D) : ℕ) : ℝ) := by positivity
    calc (ρ : ℝ) * (m : ℝ) ^ D * Real.log Q = Real.log ((Q ^ (ρ * m ^ D) : ℕ) : ℝ) := by
          rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
      _ ≤ Real.log ((P.Bl (m * a) (m * b) (Real.exp (t * m))).ncard : ℝ) :=
          Real.log_le_log hQ' (by exact_mod_cast hn)
