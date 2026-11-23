import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftDim

private theorem connectedSpace_primeSpectrum (R : Type) [CommRing R] [IsLocalRing R] :
    ConnectedSpace (PrimeSpectrum R) := by
  have : PreconnectedSpace (PrimeSpectrum R) :=
    ⟨isPreconnected_of_forall (IsLocalRing.closedPoint R) fun y _ =>
      ⟨closure {y}, Set.subset_univ _, (IsLocalRing.specializes_closedPoint y).mem_closure, subset_closure rfl,
        isPreconnected_singleton.closure⟩⟩
  exact ⟨inferInstance⟩

theorem smoothOfRelativeDimension_of_isGrpPullback : ∀ (R' O : Type) [CommRing R'] [IsLocalRing R'] [CommRing O] [Nontrivial O] (π : R' →+* O) (G : Over (Spec (CommRingCat.of R'))) [GrpObj G] (G' : Over (Spec (CommRingCat.of O))) [GrpObj G'] (ψ : G'.left ⟶ G.left) (g : ℕ), IsAbelianScheme G → Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom π)) ψ → SmoothOfRelativeDimension g G'.hom → SmoothOfRelativeDimension g G.hom := by
  intro R' O _ _ _ _ π G _ G' _ ψ g hG hp hg
  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace (Spec (CommRingCat.of R')) := connectedSpace_primeSpectrum R'
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨n, hn⟩ := Geo.Tor.exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have hn' : SmoothOfRelativeDimension n G'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback hp.1 hn
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum O) := inferInstance
  have e : n = g := H1.dim_unique _ hn' hg ((η[G']).left p)
  exact e ▸ hn

end GlobalTheory.LiftDim
