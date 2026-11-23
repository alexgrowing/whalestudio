import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompoundMatrixCauchyBinetProperties
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compoundMatrix_cauchyBinet_properties : ∀ (n l : ℕ) (g h : Matrix (Fin n) (Fin n) ℂ), cmp l (g * h) = cmp l g * cmp l h ∧ cmp l gᴴ = (cmp l g)ᴴ ∧ cmp l (1 : Matrix (Fin n) (Fin n) ℂ) = 1 ∧ ∀ f : Fin l → Fin n → ℂ, cmp l g *ᵥ wedge f = wedge (fun b => g *ᵥ f b) := by
  first | exact @GlobalTheory.compound_properties | exact GlobalTheory.compound_properties | (intros; apply GlobalTheory.compound_properties <;> assumption)
