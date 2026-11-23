import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorOfMemIsotypicComponent
import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
open Formalism.L2 Formalism.AUTREP ReciprocityTheory.Aut NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_vector_of_mem_isotypic_component : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (K : Set (GAf L n)), NG.IsIrrRep ρ S → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) → ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  first | exact @GlobalTheory.IsoFix.fixed_of_isoTyp | exact GlobalTheory.IsoFix.fixed_of_isoTyp | (intros; apply GlobalTheory.IsoFix.fixed_of_isoTyp <;> assumption)
