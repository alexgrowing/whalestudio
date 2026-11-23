import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftVolumeBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionSeparation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSeparatedSmallCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionsRank

namespace PositivityTheory.Pf1.MbRank

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def ShiftSectionsRankUpper.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → P0 ≤ mCoordIdeal y →
    IsSemipositiveRel P0 (mCoordIdeal y) A →
    ∀ q : ℕ, 1 ≤ q → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (Module.finrank ℤ (chartLat y (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a n) : ℝ) ≤
          ((genDeg (mCoordIdeal y) D (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a : ℝ) + ε) *
            ((n : ℝ) ^ D / (D.factorial : ℝ))

def ShiftSectionsRankB.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → P0 ≤ mCoordIdeal y →
    IsSemipositiveRel P0 (mCoordIdeal y) A →
    ∀ q : ℕ, 1 ≤ q →
      Tendsto (fun n : ℕ =>
          (Module.finrank ℤ (chartLat y (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a n) : ℝ) /
            ((n : ℝ) ^ D / (D.factorial : ℝ))) atTop
        (𝓝 (genDeg (mCoordIdeal y) D (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a : ℝ))

theorem ShiftSectionsRankUpper.of_B (h : ShiftSectionsRankB.Statement) : ShiftSectionsRankUpper.Statement := by
  intro K _ ι _ Ω _ y D A P0 hV hB hP0 hs q hq ε hε
  have hr := h K ι Ω y D A P0 hV hB hP0 hs q hq
  filter_upwards [hr.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε)), eventually_ge_atTop 1] with n hn hn1
  have hx : 0 < (n : ℝ) ^ D / (D.factorial : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  exact ((div_lt_iff₀ hx).1 hn).le

end

end PositivityTheory.Pf1.MbRank
