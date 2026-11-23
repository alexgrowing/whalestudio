import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuspidalRangeOfReducedFacts
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def CSize.Inv {X : CData} (S : CSize X) : Prop := ∀ γ ∈ X.I.GFset, ∀ y, S.tau1 (γ * y) = S.tau1 y

def CSize.Lip {X : CData} (S : CSize X) : Prop :=
  ∀ y g, X.φ g ≠ 0 →
    S.tau1 y * Real.exp (-(1 / (X.I.f : ℝ)) * ∑ v, cartanDistance (X.I.ε v) (g.1 v)) ≤ S.tau1 (y * g)

def CSize.LowN {X : CData} (S : CSize X) : Prop :=
  ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ x, ∃ c : ℝ, 0 < c ∧ ∀ m ∈ X.I.NA W, c ≤ S.tau1 (m * x)

theorem cu_count_of_pack (X : CData) (hn : 1 ≤ X.I.n) (S : CSize X) (hst : S.Strata) (hP : S.PackCount) (y : X.I.GA) :
    X.FarCount (cu.Act X (S.tau1 y)) (2 * (X.I.n : ℝ) ^ 2) {y} := by
  intro x hx r hr T hT
  obtain rfl : x = y := hx
  have hτ := hst.2.2.2.2.2.1 x
  have hs : (1 : ℝ) ≤ Real.sqrt (X.I.n : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have h1 := hP x r hr T hT
  have h2 := Formalism.HermitianLatticeCounting.Final.S7.farCount (InfinitePlace X.I.F) X.I.n r (S.tau1 x) (Real.sqrt (X.I.n : ℝ)) hτ.1
    (by linarith [hτ.2]) hs hr
  have hsq1 : S.tau1 x ^ 2 ≤ 1 := pow_le_one₀ hτ.1.le (by linarith [hτ.2])
  have hbase1 : 1 ≤ 3 * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2 := by
    have := hτ.1
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hA : (3 * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * Fintype.card (InfinitePlace X.I.F)) ≤
      cu.Act X (S.tau1 x) :=
    pow_le_pow_right₀ hbase1 (Nat.mul_le_mul_left _ (card_infinite_places_le_degree X.I))
  calc (T.card : ℝ) ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ cu.Act X (S.tau1 x) * Real.exp (2 * (X.I.n : ℝ) ^ 2 * ∑ v, r v) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le

theorem cu_sizeStep_of (X : CData) (hn : 1 ≤ X.I.n) (S : CSize X) (hst : S.Strata)
    (hP : S.PackCount) (hI : S.Inv) (hL : S.Lip) (hN : S.LowN) : cu.SizeStep X :=
  ⟨S.tau1, fun y => (hst.2.2.2.2.2.1 y).1, hI, cu_count_of_pack X hn S hst hP, hL, hN⟩

end Formalism.MainNotions.LeviCoordinates
