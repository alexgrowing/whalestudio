import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorSectionNonzeroLocus
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
theorem _root_.GlobalTheory.T.cartier_divisor_section_nonzero_locus : ∀ (X Z : Scheme.{0}) [IsIntegral X] (B : ReciprocityTheory.ChartRestriction.G.Semi.LB X), B.IsLB →
    ∀ (R : B.ι → X.functionFieldˣ), GlobalTheory.Cartier.IsRatSec B R → ∀ (f : X.functionField) (i : Z ⟶ X),
    (∀ (z : Z) (a : B.ι), i z ∈ B.U a → GlobalTheory.Cartier.RegAt (i z) (f * R a)) →
    ∃ s : (B.pull i).Sec, ∀ (z : Z) (a : B.ι), i z ∈ B.U a →
      (z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ GlobalTheory.Cartier.UnitAt (i z) (f * R a)) := by
  first | exact @GlobalTheory.PullRatSec.exists_sec_pull | exact GlobalTheory.PullRatSec.exists_sec_pull | (intros; apply GlobalTheory.PullRatSec.exists_sec_pull <;> assumption)
