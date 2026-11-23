import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsArithmeticVarietyAltAlt
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_isFlagBundle_isArithVar : ∀ (k : Type) [CommRing k] (B : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp k) (d : ℕ), IsArithVar q d →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B → ∀ (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ),
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
      IsFlagBundle π E r fl ∧ IsArithVar (π ≫ q) (d + ∑ a, r a * (r a - 1) / 2) ∧
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := by
  first | exact @GlobalTheory.FlagEx.main | exact GlobalTheory.FlagEx.main | (intros; apply GlobalTheory.FlagEx.main <;> assumption)
