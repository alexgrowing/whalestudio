import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.LandherrStIffLandherr
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardPeriodSpacesFamilyUniformisationLeStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpacesStatement

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem log_card_comp_unf_le : GlobalTheory.Published.HasseNormSt → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ξ : E) (AA : Submodule (𝓞 E) E), FD.cc ξ = -ξ → ξ ≠ 0 → AA.FG → AA ≠ ⊥ → (∀ x : E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x) → ∀ L : ℝ, 16 ≤ FD.fdeg E → 2 ≤ L → Real.log (FD.dE E) ≤ 4 * FD.fdeg E * L → Real.log r ≤ L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log l.M' ≤ 30 * L → Real.log (Fintype.card U.Comp) ≤ 41 * (FD.fdeg E * r * L) ^ 2 := by
  intro hH hT hO E _ _ _ H D l Xo c σ r U hr hG hU ξ AA hcc hξ hfg hbot hdual L hdeg hL hdE hr' hdg hM

  obtain ⟨g, ty, F, hty, hcard⟩ := GlobalTheory.T.exists_familyUnif_isTypeFn_card_comp_le hO E H D l Xo c σ r U hr hG hU
  have hU' := hU
  unfold Formalism.L2.PjFree.IsUnf at hU'
  have hrank : r = D.p + D.q := hU'.1
  have hemb := hG
  unfold Formalism.L2.PjFree.GoodEmb at hemb

  have key := (GlobalTheory.T.card_periodSpaces_familyUniformisation_le hH hT hO E H D l Xo _ g ty (hrank ▸ hr) hemb hty F r hrank ξ AA hcc hξ
    hfg hbot hdual).2 L hdeg hL hdE hr' hdg hM
  rcases Nat.eq_zero_or_pos (Fintype.card U.Comp) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    positivity
  · refine le_trans (Real.log_le_log (by exact_mod_cast hpos) ?_) key
    exact_mod_cast hcard

end GlobalTheory
