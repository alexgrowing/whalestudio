import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.CcMemOfK1loc
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem cc_resV {ι κ R : Type} [Semiring R] (f : κ → ι) (Th : MvPowerSeries ι R) :
    MvPowerSeries.constantCoeff (resV f Th) = MvPowerSeries.constantCoeff Th := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show MvPowerSeries.coeff (Finsupp.mapDomain f 0) Th = _
  rw [Finsupp.mapDomain_zero]

end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
