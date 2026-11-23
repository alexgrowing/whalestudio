import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLFactorProductBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_l_factor_product_bounded : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (s : ℕ), 2 ≤ s → ∃ C : ℝ, ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∏ v ∈ S, ‖Lv (fun _ : HeightOneSpectrum (𝓞 E) => ({1} : Multiset ℂˣ)) v (s : ℂ)‖ ≤ C := by
  first | exact @GlobalTheory.ZetaPartial.prod_norm_Lv_le | exact GlobalTheory.ZetaPartial.prod_norm_Lv_le | (intros; apply GlobalTheory.ZetaPartial.prod_norm_Lv_le <;> assumption)
