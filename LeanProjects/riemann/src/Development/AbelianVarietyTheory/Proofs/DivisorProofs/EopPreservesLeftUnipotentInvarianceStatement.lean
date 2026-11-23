import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EopPreservesLeftUnipotentInvariance
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eop_preserves_left_unipotent_invariance : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (f : Sm E a), (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) → ∀ (τ : E →+* ℂ) (i j : Fin a) (x : BlockIx a r → Ad E) (g : GA E a), (Eop τ i j f).1 (unip x * g) = (Eop τ i j f).1 g := by
  first | exact @GlobalTheory.CuspRep.UnipInv.Eop_unip_left | exact GlobalTheory.CuspRep.UnipInv.Eop_unip_left | (intros; apply GlobalTheory.CuspRep.UnipInv.Eop_unip_left <;> assumption)
