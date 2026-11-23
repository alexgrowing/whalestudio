import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaHaarModulusCmFieldElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_formula_haarModulus_cmField_element : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ u : E, u ≠ 0 → (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => modu (Fv F v ⊗[F] E) (inclR (Fv F v) u)).Finite ∧ modu (Ainf F ⊗[F] E) (inclR (Ainf F) u) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), modu (Fv F v ⊗[F] E) (inclR (Fv F v) u) = 1 := by
  first | exact @GlobalTheory.GaugeEx.prod_modu_inclR | exact GlobalTheory.GaugeEx.prod_modu_inclR | (intros; apply GlobalTheory.GaugeEx.prod_modu_inclR <;> assumption)
