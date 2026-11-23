import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.SphTheta.UnramQuad

theorem ord_unifUnit_of_residueCard_eq_sq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → residueCard E = residueCard F ^ 2 → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hfin _ hcard
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hq : 1 < residueCard F := one_lt_residueCard (K := F)
  have hf : residueDegree F E = 2 := by
    have h : residueCard E = residueCard F ^ residueDegree F E :=
      card_residueField_eq_pow_residueDegree F E
    rw [hcard] at h
    exact (Nat.pow_right_injective hq h).symm
  have he : ramificationIndex F E = 1 := by
    have h := ramificationIndex_mul_residueDegree F E
    rw [hf, hfin] at h
    omega
  have h := ord_algebraMap (K := F) (L := E) (unifUnit F : F)
  rw [he, ord_unifUnit] at h
  simpa using h

end GlobalTheory.CompanionTheory.SphTheta.UnramQuad
