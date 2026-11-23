import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqEmptyAddSumOfPrimeIncrements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveClIsHomogeneous
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.CovTest

open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr

theorem testVal_of_hhTest : ∀ r : ℝ, ∀ (D : D7) (Y : DV.ShimX D.what₂.Tau) (Φ : ℝ → Fn Y) (hh : Fn Y), 2 < D.R.f * (Y.N - 1) → LimFam Φ → Propor Y → HhTest Y hh → LatAt Y → PrimeLocalCondition Y → PrimeLocalSplitCondition Y → SiegRead Y → DRAt Y r → TestVal Φ hh r := by
  intro r D Y Φ hh hf hlim hprop hhh hlat h4 h1 hread hdr
  have hι : 0 < Fintype.card D.what₂.Tau := by
    rw [D.what₂.card_Tau]
    exact Nat.pos_of_ne_zero fun h => by simp [h] at hf
  obtain ⟨m, hm, hQ⟩ := GlobalTheory.Mean4.WholeShift.curveCl_isHomogeneous (N := Y.N) hι Y.j Y.j_pos Y.j_lt
  have hQ' : (curveCl D.what₂.Tau Y.N Y.j).IsHomogeneous (dimFl D.what₂.Tau Y.N - 1) := by
    have : m = dimFl D.what₂.Tau Y.N - 1 := by omega
    rw [← this]; exact hQ
  have hch : Y.chern (chLieA D _ Y.j 1 * curveCl D.what₂.Tau Y.N Y.j) = 2 * Y.vol * testI Y := by
    rw [GlobalTheory.Mean4.WholeShift.chLieA_one, hprop, GlobalTheory.Mean4.WholeShift.degFl_neg_lamA_mul]
    unfold testI
    ring
  refine GlobalTheory.Mean4.testVal_of_parts D Y Φ hh (fun T R => sieg Y T (max R 2) - Y.vol * bcFl Y) (bcFl Y) r hlim ?_ hhh ?_ ?_
  · intro B hB
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    rw [max_eq_left hR, add_sub_cancel]
    exact hlat B hB R hR
  · have := (hdr.comp (tendsto_atTop_mono (fun R => le_max_left R 2) tendsto_id)).sub_const (Y.vol * bcFl Y)
    rwa [show Y.vol * bcFl Y - 2 * r * Y.vol * testI Y - Y.vol * bcFl Y = -2 * r * Y.vol * testI Y by ring] at this
  · intro T p R hp hpT hT
    have hR : (2 : ℝ) ≤ max R 2 := le_max_right R 2
    obtain ⟨e1, e2⟩ := hread T (max R 2) p hp hpT hT
    have k1 := h1 T (max R 2) hR p hp (curveCl D.what₂.Tau Y.N Y.j)
    have k4 := h4 T (max R 2) hR p hp (curveCl D.what₂.Tau Y.N Y.j) hQ'
    show sieg Y (insert p T) (max R 2) - Y.vol * bcFl Y - (sieg Y T (max R 2) - Y.vol * bcFl Y) = _
    rw [sub_sub_sub_cancel_right, e1, e2]
    rw [mul_sub, map_sub, sub_eq_zero] at k1
    rw [← k1, ← map_sub, ← sub_mul, ← neg_sub, neg_mul, map_neg, k4, hch]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have h2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp

end GlobalTheory.CovTest
