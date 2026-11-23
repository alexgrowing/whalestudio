import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGramPosDefQuotient
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_hodge_gram_pos_def_quotient : ∀ {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ), (1 - Zᴴ * Z).PosDef → (1 - Z.map (starRingEnd ℂ) * Zᵀ).PosDef ∧ (1 - Zᵀ * Z.map (starRingEnd ℂ)).PosDef ∧ GlobalTheory.HermFrame.quotGram (modelHodgeGram Z) = (1 - Z.map (starRingEnd ℂ) * Zᵀ)⁻¹ ∧ -GlobalTheory.HermFrame.subGram (modelHodgeGram Z) = 1 - Zᵀ * Z.map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.modelHodgeGram_blocks | exact GlobalTheory.modelHodgeGram_blocks | (intros; apply GlobalTheory.modelHodgeGram_blocks <;> assumption)
