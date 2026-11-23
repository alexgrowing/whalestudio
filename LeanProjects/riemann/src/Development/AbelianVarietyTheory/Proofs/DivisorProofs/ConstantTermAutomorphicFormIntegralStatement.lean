import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_automorphic_form_integral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) ∈ Sm E a ∧ ∀ (X : Lie E a) (g : GA E a), lieD X (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.ConstTermSmooth.constTerm_mem_Sm | exact GlobalTheory.ConstTermSmooth.constTerm_mem_Sm | (intros; apply GlobalTheory.ConstTermSmooth.constTerm_mem_Sm <;> assumption)
