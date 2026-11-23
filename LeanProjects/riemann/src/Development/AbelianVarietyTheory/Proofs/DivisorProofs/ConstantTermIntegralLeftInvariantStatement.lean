import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermIntegralLeftInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_integral_left_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ f : GA E a → ℂ, (∀ γ g, f (ratGL E a γ * g) = f g) → ∀ (γ : GL (Fin r) E × GL (Fin (a - r)) E) (g : GA E a), ∫ x in 𝓕, f (unip x * (ratGL E a (GlobalTheory.LeviGA.blkGL hr γ) * g)) ∂μ = ∫ x in 𝓕, f (unip x * g) ∂μ := by
  first | exact @GlobalTheory.LeviConstTerm.constTerm_levi_invariant | exact GlobalTheory.LeviConstTerm.constTerm_levi_invariant | (intros; apply GlobalTheory.LeviConstTerm.constTerm_levi_invariant <;> assumption)
