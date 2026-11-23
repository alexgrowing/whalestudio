import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNonvanishingClosedPoints
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedBasePt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootHeightLeAbelianHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearCombStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundedBelowOffZeroLocusStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts GlobalTheory.ShFam.Pad
open CategoryTheory AlgebraicGeometry GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.Cartier
open scoped Classical
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_nonvanishing_closed_points : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (L : GlobalTheory.HermLB V.p) (r : (L.B.pull V.j).ι → V.G.functionFieldˣ), GlobalTheory.Cartier.IsRatSec (L.B.pull V.j) r → (∀ i, ∀ x ∈ (L.B.pull V.j).U i, UnitAt x (r i : V.G.functionField)) → ∃ (s : L.B.Sec) (s' : L.dual.B.Sec), ∀ w : V.G, IsClosed ({w} : Set V.G) → V.j w ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ∧ V.j w ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s' := by
  first | exact @GlobalTheory.RatSecClear.exists_secs_nonvanishing | exact GlobalTheory.RatSecClear.exists_secs_nonvanishing | (intros; apply GlobalTheory.RatSecClear.exists_secs_nonvanishing <;> assumption)
