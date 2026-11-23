import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiRankBounds.Development

namespace PositivityTheory.Pf1.MbRank

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem ShiftVolumeBound.of_upper (hSep : ShiftSectionSeparation.Statement)
    (hCount : SeparatedSmallCount.Statement) (hRank : ShiftSectionsRankUpper.Statement) :
    ShiftVolumeBound.Statement := by
  intro K _ ι _ Ω _ y D A P0 hD hV hB hP hS hN hC
  obtain ⟨C, hC0, hsep⟩ := hSep K ι Ω y D A hV hB hS.1
  refine ⟨2 * (C + 1) * ((D : ℝ) + 1), by positivity, ?_⟩
  intro q hq
  have hcount : ∀ n : ℕ,
      smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) (↑q) 1))
          (chartLat y (HermLine.zcomb A (fsH ι) (↑q) 1).a) n ≤
        (Module.finrank ℤ ↥(chartLat y (HermLine.zcomb A (fsH ι) (↑q) 1).a n) : ℝ) *
          ((C + 1) * n * ((q : ℝ) + 1) + Real.log 3) := by
    intro n
    refine hCount K ι Ω y D (HermLine.zcomb A (fsH ι) (↑q) 1) n ((C + 1) * n * ((q : ℝ) + 1))
      hV hB (by positivity) ?_
    intro s hs hs0 c hc
    refine hsep q hq n s hs hs0 c (lt_of_lt_of_le hc (Real.exp_le_exp.mpr ?_))
    have : (0 : ℝ) ≤ n * ((q : ℝ) + 1) := by positivity
    nlinarith
  unfold arVolP
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hK : (0 : ℝ) < 2 * (C + 1) * ((D : ℝ) + 1) * ((q : ℝ) + 1) := by positivity
  have hε : (0 : ℝ) < δ / (2 * (C + 1) * ((D : ℝ) + 1) * ((q : ℝ) + 1)) := div_pos hδ hK
  have hr := hRank K ι Ω y D A P0 hV hB hP hS q hq _ hε
  apply Filter.limsup_le_of_le
  · exact Filter.isCoboundedUnder_le_of_le atTop (x := 0) (fun k => div_nonneg
      (Real.log_natCast_nonneg _) (by positivity))
  · filter_upwards [hr, eventually_ge_atTop 2] with n hn hn2
    simp only [one_mul]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hlog : Real.log 3 ≤ (C + 1) * n * ((q : ℝ) + 1) := by
      have h1 : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      have h2 : (0 : ℝ) ≤ C * n * ((q : ℝ) + 1) := by positivity
      nlinarith
    have hR0 : (0 : ℝ) ≤ (Module.finrank ℤ ↥(chartLat y (HermLine.zcomb A (fsH ι) (↑q) 1).a n) : ℝ) :=
      Nat.cast_nonneg _
    have hpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hpos]
    have hmul : (0 : ℝ) ≤ 2 * (C + 1) * n * ((q : ℝ) + 1) := by positivity
    calc smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) (↑q) 1))
          (chartLat y (HermLine.zcomb A (fsH ι) (↑q) 1).a) n
        ≤ (Module.finrank ℤ ↥(chartLat y (HermLine.zcomb A (fsH ι) (↑q) 1).a n) : ℝ) *
          ((C + 1) * n * ((q : ℝ) + 1) + Real.log 3) := hcount n
      _ ≤ 2 * (C + 1) * n * ((q : ℝ) + 1) *
          (Module.finrank ℤ ↥(chartLat y (HermLine.zcomb A (fsH ι) (↑q) 1).a n) : ℝ) := by
          nlinarith
      _ ≤ 2 * (C + 1) * n * ((q : ℝ) + 1) *
          (((genDeg (mCoordIdeal y) D (HermLine.zcomb A (fsH ι) (↑q) 1).a : ℝ) +
            δ / (2 * (C + 1) * ((D : ℝ) + 1) * ((q : ℝ) + 1))) * ((n : ℝ) ^ D / (D.factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hn hmul
      _ = (2 * (C + 1) * ((D : ℝ) + 1) * ((q : ℝ) + 1) *
            (genDeg (mCoordIdeal y) D (HermLine.zcomb A (fsH ι) (↑q) 1).a : ℝ) + δ) *
          ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
          rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
          have hf : (0 : ℝ) < (D.factorial : ℝ) := by positivity
          field_simp
          push_cast
          ring

end

end PositivityTheory.Pf1.MbRank
