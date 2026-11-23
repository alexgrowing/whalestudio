import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersAutCommHostConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOfIntegers_aut_comm_hostConjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E), τ (H.bar a) = H.bar (τ a) := by
  first | exact @GlobalTheory.ringOfIntegers_equiv_bar_comm | exact GlobalTheory.ringOfIntegers_equiv_bar_comm | (intros; apply GlobalTheory.ringOfIntegers_equiv_bar_comm <;> assumption)
