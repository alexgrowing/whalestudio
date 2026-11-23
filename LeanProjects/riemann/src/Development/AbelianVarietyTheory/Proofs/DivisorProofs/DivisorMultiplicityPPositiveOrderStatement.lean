import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorMultiplicityPPositiveOrder
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
theorem _root_.GlobalTheory.T.divisor_multiplicity_p_positive_order : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp k) (D : ℕ),
    IsArithVar q D → ∀ (M : HermLB q) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r) (p : ℕ), p.Prime →
    (∀ i, ∀ x ∈ M.B.U i, RegAt x (r i : X.functionField) ∧ (IsUnit (p : X.presheaf.stalk x) → UnitAt x (r i : X.functionField))) →
    ∀ z, (M.div hr).mult z ≠ 0 → 0 < Scheme.ord ((p : X.functionField)) z ∧
      ∀ (Z : Scheme.{0}) [IsIntegral Z] (i : Z ⟶ X), i (genericPoint Z) = z →
        ∀ (z' : Z) j, i z' ∈ M.B.U j → ¬ UnitAt (i z') (r j : X.functionField) := by
  first | exact @GlobalTheory.SuppP.suppP | exact GlobalTheory.SuppP.suppP | (intros; apply GlobalTheory.SuppP.suppP <;> assumption)
