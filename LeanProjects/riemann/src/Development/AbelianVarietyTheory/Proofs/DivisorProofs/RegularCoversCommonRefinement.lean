import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlterationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroResidueFieldGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RegCoverCommon

theorem exists_regCover_le_both : RegularAlteration → ∀ (k : Type) [CommRing k] (B : Scheme.{0}) [IsIntegral B]
    (q : B ⟶ Sp k), IsArithVar q 1 → ∀ C₁ C₂ : RegCover q, ∃ C : RegCover q,
      (∃ t₁ : C.Y ⟶ C₁.Y, t₁ ≫ C₁.ρ = C.ρ) ∧ ∃ t₂ : C.Y ⟶ C₂.Y, t₂ ≫ C₂.ρ = C.ρ := by
  intro hRA k _ B _ q hq C₁ C₂
  obtain ⟨Z, hZ, t₁, t₂, e, hZa, g₁, g₂, d₁, d₂⟩ := RegCover.exists_common hq C₁ C₂
  obtain ⟨D⟩ := GlobalTheory.T.exists_regular_cover_of_alteration hRA k Z ((t₁ ≫ C₁.ρ) ≫ q) hZa
  refine ⟨⟨D.Y, D.ρ ≫ t₁ ≫ C₁.ρ, ?_, ?_, ?_⟩, ⟨D.ρ ≫ t₁, by simp⟩, ⟨D.ρ ≫ t₂, by simp [e]⟩⟩
  · simpa [Category.assoc] using D.reg
  · simp only [Scheme.Hom.comp_apply]
    rw [D.generic, g₁, C₁.generic]
  · rw [CurveDegreesCompare.residueDegree_comp, CurveDegreesCompare.residueDegree_comp, D.generic, g₁]
    exact mul_ne_zero (mul_ne_zero C₁.finite d₁) D.finite

end GlobalTheory.RegCoverCommon
