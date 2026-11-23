import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelDensitiesOfHermitianFormStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem siegelWeilUnitaryConvergent : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent :=
  fun F E _ _ _ _ _ σ hσ M J hJ =>
    ⟨finVol_unitaryGroup F E σ hσ M J hJ, GlobalTheory.T.siegel_densities_of_hermitian_form F E σ hσ M J hJ⟩

end GlobalTheory.CompanionTheory.SW
