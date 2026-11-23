import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralAndIsNormalSchemeOfSmoothDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfRatPoint

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.NeutralPart

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.SS.NeutralPart.geometricallyConnected_of_section {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [QuasiCompact f] (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
    (h : ∀ s : S, _root_.IsConnected (f ⁻¹' {s})) : GeometricallyConnected f := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro s
  haveI : ConnectedSpace (f ⁻¹' {s}) := isConnected_iff_connectedSpace.mp (h s)
  haveI : ConnectedSpace (f.fiber s) :=
    (f.fiberHomeo s).symm.surjective.connectedSpace (f.fiberHomeo s).symm.continuous
  haveI : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    instLocallyOfFiniteTypeSndScheme f (S.fromSpecResidueField s)
  exact _root_.GlobalTheory.RatPointConn.of_section (k := S.residueField s)
    (f.fiberToSpecResidueField s)
    (pullback.lift (S.fromSpecResidueField s ≫ e) (𝟙 _) (by simp [he]))
    (pullback.lift_snd _ _ _)

end GlobalTheory.SS.NeutralPart
