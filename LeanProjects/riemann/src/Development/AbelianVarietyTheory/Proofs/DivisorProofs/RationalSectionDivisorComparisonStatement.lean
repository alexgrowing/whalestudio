import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorComparison
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOfRationalSectionViaDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSubschemePrimeFibreStatement
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_divisor_comparison : ∀ (X : Scheme.{0}) [IsIntegral X] (k : Type) [CommRing k] (q : X ⟶ Sp k) (M : HermLB q)
    (r : M.B.ι → X.functionFieldˣ), (∀ i, ∀ x ∈ M.B.U i, RegAt x (r i : X.functionField)) →
    ∀ (B : HermLB q) (ρ : B.B.ι → X.functionFieldˣ), IsRatSec B.B ρ → ∀ (ι : Type) (U : ι → X.Opens) (t : ι → X.functionFieldˣ),
    (∀ i, ∀ x ∈ M.B.U i, ¬ UnitAt x (r i : X.functionField) → (∃ a, x ∈ U a) ∧
      (∀ a j, x ∈ U a → x ∈ B.B.U j → UnitAt x ((t a : X.functionField) * ρ j)) ∧
      ∀ a b, x ∈ U a → x ∈ U b → RegAt x (((t a / t b : X.functionFieldˣ) - 1 : X.functionField) / r i)) →
    ∀ (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i],
      (∀ (z' : Z) j, i z' ∈ M.B.U j → ¬ UnitAt (i z') (r j : X.functionField)) →
      cls (B.B.pull i) (LB.isLB_pull B.isLB i) = 0 := by
  first | exact @GlobalTheory.TrivOnZeroLocus.cls_pull_eq_zero | exact GlobalTheory.TrivOnZeroLocus.cls_pull_eq_zero | (intros; apply GlobalTheory.TrivOnZeroLocus.cls_pull_eq_zero <;> assumption)
