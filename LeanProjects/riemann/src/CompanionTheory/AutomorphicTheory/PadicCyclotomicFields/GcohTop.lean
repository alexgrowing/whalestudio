import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohField
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohMu
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTate
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohFin

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

theorem top_tate : Formalism.GaloisCohomology.LocalTateDualityK := tate_of gcRep gc0 gc1 gc2 gcField gcMu

theorem top_locfin : Formalism.GaloisCohomology.LocalFinitenessK := locfin_of gcField

end CompanionTheory.LocalTateOrthogonality.Gcoh
