import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.KollarApp

theorem sum_Icc_cast_eq_choose (n : ℕ) :
    ∑ e ∈ Finset.Icc 1 n, (e : ℝ) = (((n + 1).choose 2 : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.choose_succ_succ (n + 1) 1]
    simp
    ring

theorem isolatedNonKlt_smooth : GlobalTheory.Published.IsolatedNonKltDivisor → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → 1 ≤ D → letI := algebraΓOfHom q; ∀ (N₀ : LB X) (r : ℕ) (x : X), 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → IsClosed ({x} : Set X) → (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → (((D + 1).choose 2 : ℕ) : ℝ) ^ e < (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e) → ∃ (m' : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m' ∧ D₀.Eff ∧ (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = interNumRed ℂ C ![N₀] / r) ∧ x ∈ U ∧ (∀ y ∈ U, y ≠ x → KltAt q D (qWeil D₀ m') y) ∧ ¬ KltAt q D (qWeil D₀ m') x := by
  intro hK X _ _ q D _ hproj hD
  letI := algebraΓOfHom q
  intro N₀ r x hr hnef hbig hx hint
  haveI := SmoothOfRelativeDimension.smooth D q
  haveI : GlobalTheory.IsNormalScheme X := isNormalScheme_of_smooth q
  have hdim : topologicalKrullDim X = D := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q D inferInstance
  have hc : (0 : ℝ) < (((D + 1).choose 2 : ℕ) : ℝ) := by
    have : 0 < (D + 1).choose 2 := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hsum : ∑ e ∈ Finset.Icc 1 D, (e : ℝ) / (((D + 1).choose 2 : ℕ) : ℝ) ≤ 1 := by
    rw [← Finset.sum_div, sum_Icc_cast_eq_choose, div_self hc.ne']
  obtain ⟨m, D₀, U, hm, hD₀, hnum, hxU, -, hklt, hnot⟩ :=
    hK X q D hproj hdim hD 0 r N₀ x (fun _ => (((D + 1).choose 2 : ℕ) : ℝ))
      ⟨by simp, fun z hz => absurd rfl hz, fun _ => le_rfl⟩
      (fun y => GlobalTheory.Discrepancy.kltAt_zero_of_smooth hdim y) hr hnef hbig hx (fun _ _ => hc)
      hint hsum
  refine ⟨m, D₀, U, hm, hD₀, hnum, hxU, fun y hy hyx => ?_, ?_⟩
  · simpa using hklt y hy hyx
  · simpa using hnot

end GlobalTheory.KollarApp
