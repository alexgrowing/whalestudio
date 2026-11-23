import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedLevelCoverExistsConstantsDominantWeigStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelCoverUniformisationDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPinsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false

namespace GlobalTheory.CoverExists

theorem exists_ext_of_le {K L : IntermediateField ℚ ℂ} [FiniteDimensional ℚ L] (hle : K ≤ L) (σ : K →+* ℂ) :
    ∃ σ' : L →+* ℂ, σ'.comp (IntermediateField.inclusion hle).toRingHom = σ := by
  letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : IsScalarTower ℚ K L :=
    IsScalarTower.of_algebraMap_eq (fun x => ((IntermediateField.inclusion hle).commutes x).symm)
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  refine ⟨(IsAlgClosed.lift : L →ₐ[K] ℂ).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : L →ₐ[K] ℂ).commutes x

end GlobalTheory.CoverExists

namespace GlobalTheory.CoverExists

end GlobalTheory.CoverExists
