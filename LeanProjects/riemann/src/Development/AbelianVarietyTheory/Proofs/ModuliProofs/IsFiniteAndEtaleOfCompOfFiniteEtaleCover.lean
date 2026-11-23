import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem isFinite_and_etale_of_comp_of_finite_etale_cover :
    ∀ (X Y Z : Scheme.{0}) (q : X ⟶ Y) (π : Y ⟶ Z), IsFinite q → Etale q → Surjective q → IsFinite (q ≫ π) → Etale (q ≫ π) → IsSeparated π → LocallyOfFinitePresentation π → IsFinite π ∧ Etale π := by
  intro X Y Z q π _ _ _ _ _ _ _
  have he : Etale π := GlobalTheory.etale_of_comp_of_etale_of_surjective q π
  have : UniversallyClosed π := UniversallyClosed.of_comp_surjective q π
  have : IsProper π := {}
  have : LocallyQuasiFinite π := by
    refine ⟨fun {U} hU {V} hV e => ?_⟩
    have h₁ := π.formallyUnramified_appLE hU hV e
    have h₂ := π.finiteType_appLE hU hV e
    algebraize [(π.appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  exact ⟨.of_isProper_of_locallyQuasiFinite _, he⟩

end GlobalTheory.HkFam
