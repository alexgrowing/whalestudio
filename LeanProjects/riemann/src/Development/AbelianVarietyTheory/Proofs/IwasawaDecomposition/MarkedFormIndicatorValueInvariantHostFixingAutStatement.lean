import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorValueInvariantHostFixingAut
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedFormIndicatorValue_invariant_hostFixingAut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ lab : InvFun (𝓞 E)) (i : ℕ), IsTwInv H ψ → IsTwInv H lab → ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 → ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), markVal H.bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal H.bar ψ lab i n B := by
  first | exact @GlobalTheory.PolFan.Mark.markVal_twist | exact GlobalTheory.PolFan.Mark.markVal_twist | (intros; apply GlobalTheory.PolFan.Mark.markVal_twist <;> assumption)
