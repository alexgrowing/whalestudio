import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsArithmeticVarietyAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalMetrizedBundleFlagPullbackStatement

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt
open GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open scoped Classical

namespace GlobalTheory.CovTest.BunModelEx

theorem choose_two_add (j : ℕ) : ∀ m : ℕ, (j + m).choose 2 = j.choose 2 + m.choose 2 + j * m
  | 0 => by simp
  | m + 1 => by
    rw [← add_assoc, Nat.choose_succ_succ, choose_two_add j m, Nat.choose_one_right, Nat.choose_succ_succ m 1,
      Nat.choose_one_right]
    ring

theorem dim_sum {D : D7} (O : Setup D) (c : O.s.Comp) :
    dimGr D.what₂.Tau O.N O.j + ∑ a : D.what₂.Tau × Bool, rkB D.what₂.Tau O.N O.j a * (rkB D.what₂.Tau O.N O.j a - 1) / 2 =
      (O.var c).dim := by
  rw [show (O.var c).dim = _ from O.dim_eq c, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, rkB, cond_true, cond_false, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  unfold dimGr Formalism.DegreeFormula.dimFl
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right]
  obtain ⟨hj, hN⟩ := O.indef
  have e : O.N = O.j + (O.N - O.j) := by omega
  conv_rhs => rw [e]
  rw [choose_two_add]
  ring

theorem bunSt_holds : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → BunSt := by
  intro h1 h2 h3 h4 D O hO B hB R hR c
  obtain ⟨Bs, hBs, q, ar, nB, E, h, H, hBC⟩ := GlobalTheory.T.toroidal_metrized_bundle_flag_pullback h1 h2 h3 h4 D O hO B hB R hR c
  obtain ⟨Y, hY, π, fl, univ, arY, nY⟩ :=
    GlobalTheory.T.exists_normal_isFlagBundle_isArithVar (𝓞 D.what₂.LL) Bs q _ ar nB (D.what₂.Tau × Bool) E (rkB D.what₂.Tau O.N O.j) fun a => (h a).isVB
  rw [dim_sum O c] at arY
  obtain ⟨G, hG, j, πG, pb, hf, hs, φ, φs, hind⟩ := hBC Y hY π fl univ arY nY
  exact ⟨BunModel.mk (@Cover.mk _ _ (O.var c) Y _ (π ≫ q) arY nY G _ j πG pb _ _ φ φs) Bs q ar π rfl E h H fl univ hind⟩

end GlobalTheory.CovTest.BunModelEx

end
