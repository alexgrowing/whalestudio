import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeOfPolyAsymptotics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendstoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonnegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivialStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_two_le_lc_one_add (hHS : GlobalTheory.Published.ArithHilbertSamuel) (hA : GlobalTheory.Published.ArCalc) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (P : Pair p) (b : ℕ)
    (s t : X.functionField) (hG : P.Good D b s t) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      P.lc 0 (b * (n * m : ℕ) + m) 2 ≤ P.lc 0 (b * (n * m : ℕ)) 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  obtain ⟨h, hh⟩ := (hA.1 k X p D hX).1 P.A
  have hα : P.A.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
  have hnef := GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg k X p D hX P.A 0 le_rfl hG.nef
  have hrep : P.Rep 0 1 P.A := (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
  have key := GlobalTheory.eventually_le_of_poly_asymptotics (D + 1) b
    (fun η j => P.lc 0 (j : ℤ) (Real.exp (η * j))) (fun j => P.lc 0 (j : ℤ) 2)
    (h (genericPoint X) / (D + 1).factorial) ((D + 1) * gdeg P.A D / (D + 1).factorial) (Nat.succ_pos D) hG.pos
    (fun η hη => by
      have := GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hA k X p D hX P 0 1 P.A (h (genericPoint X)) 0 hrep hα hnef η hη
      simpa only [mul_zero, mul_one] using this)
    (fun η hη => by
      have h1 : ∀ᶠ j : ℕ in atTop, Real.log 2 ≤ η * j :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hη).eventually_ge_atTop _
      filter_upwards [h1] with j hj
      have h2 : (2 : ℝ) ≤ Real.exp (η * j) := by
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ _ := Real.exp_le_exp.2 hj
      have hsub : P.Bl 0 (j : ℤ) 2 ⊆ P.Bl 0 (j : ℤ) (Real.exp (η * j)) :=
        fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans h2⟩
      have hfin := GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG 0 (j : ℤ) (Real.exp (η * j)) hA
      have hle := Set.ncard_le_ncard hsub hfin
      simp only [Pair.lc]
      rcases Nat.eq_zero_or_pos (P.Bl 0 (j : ℤ) 2).ncard with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg _
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle))
    ε hε
  filter_upwards [key] with n hn
  filter_upwards [hn] with m hm
  have e1 : (((b * n + 1) * m : ℕ) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) + (m : ℤ) := by push_cast; ring
  have e2 : (((b * n * m : ℕ)) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) := by push_cast; ring
  simp only [e1, e2, zero_mul, Real.exp_zero] at hm
  exact hm

end GlobalTheory.VolBr
