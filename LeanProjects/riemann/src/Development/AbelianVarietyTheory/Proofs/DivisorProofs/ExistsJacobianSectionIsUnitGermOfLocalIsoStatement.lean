import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionIsUnitGermOfLocalIso
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jacobian_section_isUnit_germ_of_localIso : ∀ (F : Type) [Field F] (Y X : Scheme.{0}) (p : Y ⟶ Sp F) (σ : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d p] [SmoothOfRelativeDimension d (σ ≫ p)] (K : CanonLB p d) (K' : CanonLB (σ ≫ p) d),
    ∃ J : H0 (σ ≫ p) (LB.div K'.bundle (K.bundle.pull σ)) ⊤, ∀ x : X, Function.Bijective (σ.stalkMap x).hom →
      ∀ (a : (LB.div K'.bundle (K.bundle.pull σ)).ι) (ha : x ∈ (LB.div K'.bundle (K.bundle.pull σ)).U a),
        IsUnit (H0.germ a x (memTop x) ha J) := by
  first | exact @GlobalTheory.exists_jacobian_section_isUnit_germ | exact GlobalTheory.exists_jacobian_section_isUnit_germ | (intros; apply GlobalTheory.exists_jacobian_section_isUnit_germ <;> assumption)
