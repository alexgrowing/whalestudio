import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationChangePreservesAlgebraicValues
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralRuleRuleBaseChangeCoeffFieldIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComplexModelsComponentsIsometriesDegre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactification_change_preserves_algebraic_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (hle : c.F ≤ c'.F), FnAlgClosed Xo c → ∃ eC : Comp Xo c ≃ Comp Xo c', ∀ (Z : Comp Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, (GlobalTheory.CompHt.genVal (eC Z) (GlobalTheory.FieldBC.rulBC hle f) = 0 ↔ GlobalTheory.CompHt.genVal Z f = 0) := by
  first | exact @GlobalTheory.CompBC.comp_bc_genVal | exact GlobalTheory.CompBC.comp_bc_genVal | (intros; apply GlobalTheory.CompBC.comp_bc_genVal <;> assumption)
