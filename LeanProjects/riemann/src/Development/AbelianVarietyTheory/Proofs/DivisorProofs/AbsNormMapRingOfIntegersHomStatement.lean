import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMapRingOfIntegersHom
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_map_ringOfIntegers_hom' : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (𝔞 : Ideal (𝓞 E)), Module.finrank ℚ E ∣ Module.finrank ℚ K ∧ Ideal.absNorm (𝔞.map τ) = Ideal.absNorm 𝔞 ^ (Module.finrank ℚ K / Module.finrank ℚ E) := by
  first | exact @GlobalTheory.absNorm_map_ringOfIntegers_hom | exact GlobalTheory.absNorm_map_ringOfIntegers_hom | (intros; apply GlobalTheory.absNorm_map_ringOfIntegers_hom <;> assumption)
