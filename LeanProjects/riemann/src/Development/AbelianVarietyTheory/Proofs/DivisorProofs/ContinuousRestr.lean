import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
open IsDedekindDomain

namespace GlobalTheory.LKTrip

theorem AfP.continuous_restr (p : ℕ) : Continuous (AfP.restr p) :=
  RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ) Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ ↦ RingHom.id _) (Filter.Eventually.of_forall fun _ ↦ Set.mapsTo_id _)
    (fun _ ↦ continuous_id)

end GlobalTheory.LKTrip
