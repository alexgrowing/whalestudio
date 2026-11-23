import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PartIHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliSchemesExist
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexUniformisationHolds
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelMapsHeckePointsOfPos
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem modelClause_of_rankZero
    (hz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
      D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D)) :
    PartI ∧ N1ab ∧ N1c ∧
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
        ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D) := by
  refine ⟨partI_holds, moduli_schemes_exist, complex_uniformisation_holds, ?_⟩
  intro E _ _ _ H D
  by_cases h : D.p + D.q = 0
  · exact hz E H D h
  · exact levelMaps_heckePoints_of_pos E H D (by omega)

end GlobalTheory.CompanionTheory.Ar.Top
