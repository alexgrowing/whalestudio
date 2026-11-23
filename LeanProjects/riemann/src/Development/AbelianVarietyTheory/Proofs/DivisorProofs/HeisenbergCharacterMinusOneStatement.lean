import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCharacterMinusOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_character_minus_one : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (ι : Type) [Fintype ι], ∃ C : ℝ,
    ∀ x : ι → AF F, 0 < ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ → ∃ (i : ι) (a : Ainf F), ψ (x i * GlobalTheory.HeisSchA.mk a 0) = -1 ∧
      ‖InfiniteAdeleRing.ringEquiv_mixedSpace F a‖ * ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖ ≤ C := by
  first | exact @GlobalTheory.ArchHalfTurn.halfturn | exact GlobalTheory.ArchHalfTurn.halfturn | (intros; apply GlobalTheory.ArchHalfTurn.halfturn <;> assumption)
