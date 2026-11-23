import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FlatQuotientWeaklyRegular
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_quotient_weakly_regular : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (rs : List A), (∀ r ∈ rs, r ∈ maximalIdeal A) → RingTheory.Sequence.IsWeaklyRegular (A ⧸ (maximalIdeal V).map (algebraMap V A)) rs → Module.Flat V (A ⧸ Ideal.ofList rs) := by
  first | exact @GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre | exact GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre | (intros; apply GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre <;> assumption)
