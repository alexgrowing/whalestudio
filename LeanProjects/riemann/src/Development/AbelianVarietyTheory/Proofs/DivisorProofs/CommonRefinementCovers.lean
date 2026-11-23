import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalFiniteDominantRefinementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverLiftThroughNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverDominatingPairStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverCommon

theorem exists_cover_dominating_two : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V₁ V₂ : Cover Y), ∃ (V : Cover Y) (π₁ : V.X ⟶ V₁.X) (π₂ : V.X ⟶ V₂.X), π₁ ≫ V₁.p = V.p ∧ π₂ ≫ V₂.p = V.p ∧ Lies V V₁ π₁ ∧ Lies V V₂ π₂ := by
  intro F _ _ Y V₁ V₂
  obtain ⟨G, _, _, g, k, _, _, hk⟩ := GlobalTheory.T.normal_finite_dominant_refinement F Y V₁ V₂
  obtain ⟨W, a, k', ha, hW, hk'⟩ := GlobalTheory.T.cover_lift_through_normal F Y V₁ V₂ G g k hk
  obtain ⟨W', b, c, hb, hc, hW', hV⟩ := GlobalTheory.T.cover_dominating_pair F Y W V₂ k' hk'
  obtain ⟨e, he₁, he₂⟩ := hW
  obtain ⟨e', he₁', he₂'⟩ := hW'
  refine ⟨W', b ≫ a, c, by rw [Category.assoc, ha, hb], hc, ⟨e' ≫ e, ?_, ?_⟩, hV⟩
  · rw [Category.assoc, he₁, ← Category.assoc, he₁', Category.assoc]
  · rw [Category.assoc, he₂, he₂']

end GlobalTheory.CoverCommon
