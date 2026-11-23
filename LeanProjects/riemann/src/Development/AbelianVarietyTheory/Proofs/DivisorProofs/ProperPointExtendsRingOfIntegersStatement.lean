import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperPointExtendsRingOfIntegers
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts GlobalTheory.LieMet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_point_extends_ring_of_integers : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp (𝓞 F)), IsProjOver s → ∀ (K : Type) [Field K] [NumberField K] (fK : F →+* K) (yK : Sp K ⟶ X), yK ≫ s = spMap (fK.comp (algebraMap (𝓞 F) F)) → ∃ xO : Sp (𝓞 K) ⟶ X, spMap (algebraMap (𝓞 K) K) ≫ xO = yK := by
  first | exact @GlobalTheory.ProjPointExt.exists_integral_extension | exact GlobalTheory.ProjPointExt.exists_integral_extension | (intros; apply GlobalTheory.ProjPointExt.exists_integral_extension <;> assumption)
