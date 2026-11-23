import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionDegreePositiveOnCurve
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
theorem _root_.GlobalTheory.T.section_degree_positive_on_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (e : ℕ), IsArithVar p e →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
      [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → ∀ (M : ReciprocityTheory.ChartRestriction.G.Semi.LB Z), M.IsLB → ∀ s : M.Sec,
      (∃ z, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) → (∃ z, z ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) →
      0 < topSelfIntersection κ M 1 := by
  first | exact @GlobalTheory.CurveSecDeg.topSelf_pos_of_sec | exact GlobalTheory.CurveSecDeg.topSelf_pos_of_sec | (intros; apply GlobalTheory.CurveSecDeg.topSelf_pos_of_sec <;> assumption)
