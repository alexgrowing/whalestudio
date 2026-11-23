import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinitePlaceValuationCompRingEquiv
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePlace_valuation_comp_ringEquiv : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L) (la : HeightOneSpectrum (𝓞 L)), ∃ la' : HeightOneSpectrum (𝓞 K), ∀ y : K, la'.valuation K y = la.valuation L (e y) := by
  first | exact @GlobalTheory.PlaceTransport.exists_place_valuation_comp_equiv | exact GlobalTheory.PlaceTransport.exists_place_valuation_comp_equiv | (intros; apply GlobalTheory.PlaceTransport.exists_place_valuation_comp_equiv <;> assumption)
