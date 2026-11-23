import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCovers
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.common_refinement_covers : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V₁ V₂ : Cover Y), ∃ (V : Cover Y) (π₁ : V.X ⟶ V₁.X) (π₂ : V.X ⟶ V₂.X), π₁ ≫ V₁.p = V.p ∧ π₂ ≫ V₂.p = V.p ∧ Lies V V₁ π₁ ∧ Lies V V₂ π₂ := by
  first | exact @GlobalTheory.CoverCommon.exists_cover_dominating_two | exact GlobalTheory.CoverCommon.exists_cover_dominating_two | (intros; apply GlobalTheory.CoverCommon.exists_cover_dominating_two <;> assumption)
