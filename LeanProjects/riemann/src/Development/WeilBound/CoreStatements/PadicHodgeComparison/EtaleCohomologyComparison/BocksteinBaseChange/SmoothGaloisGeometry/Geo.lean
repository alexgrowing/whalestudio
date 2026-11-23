import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompactSpaceOfIsProjOver

noncomputable section

namespace CrystallineSemistableComparison

theorem comp : ModelComponents := fun l _ K _ ↦ ⟨compSm l K, compGood l K⟩

theorem geo : GeometricGenericComponents := geoMain

end CrystallineSemistableComparison
