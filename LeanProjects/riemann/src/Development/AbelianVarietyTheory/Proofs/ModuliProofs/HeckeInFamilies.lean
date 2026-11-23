import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.HeckeInFamilies
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyHeckeCorrespondenceSchemeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHeckeQuotientReducedBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeCorrespondenceSecondProjectionFiniteEtaleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernelsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransferPts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem heckeInFamilies : HeckeInFamilies := by
  intro E _ _ _ H D l Xo 𝔓 p i hr hA
  refine ⟨?_, fun S s o C j h₁ h₂ h₃ h₄ h₅ => GlobalTheory.T.existsUnique_heckeQuotient_reducedBase E H D l Xo 𝔓 p i S s o C j hr hA h₁ h₂ h₃ h₄ h₅⟩
  obtain ⟨Z⟩ := GlobalTheory.T.nonempty_heckeCorrespondenceScheme E H D l Xo 𝔓 p i hr hA
  obtain ⟨a, b, c⟩ := GlobalTheory.T.heckeCorrespondence_secondProjection_finite_etale E H D l Xo 𝔓 p i Z hr hA
  obtain ⟨d, e⟩ := GlobalTheory.T.heckeKernelScheme_geometric_points_eq_kernels E H D l Xo 𝔓 p i Z.toKerScheme hA
  exact ⟨Z, a, b, fun h => ⟨e h, c h⟩, fun k _ _ y C hC =>
    ⟨d k y C hC, fun z hz => pointQuot_snd E H D l Xo 𝔓 p i Z hA k z y C hz⟩⟩

end GlobalTheory.HkFam
