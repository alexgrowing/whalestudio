import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharCmEqOneOfTrivialDegreeOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_cm_eq_one_of_trivial_degree_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → χ = 1 := by
  first | exact @GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne | exact GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne | (intros; apply GlobalTheory.HeckeSplit.heckeChar_eq_one_of_degOne <;> assumption)
