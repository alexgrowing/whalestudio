import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsFiniteOverIntegers
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_sections_finite_over_integers : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (p : X ⟶ Sp (𝓞 F)),
    IsArithVar (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) 0 → Module.Finite ℤ Γ(X, ⊤) := by
  first | exact @GlobalTheory.GlobalFunFinite.moduleFinite_int | exact GlobalTheory.GlobalFunFinite.moduleFinite_int | (intros; apply GlobalTheory.GlobalFunFinite.moduleFinite_int <;> assumption)
