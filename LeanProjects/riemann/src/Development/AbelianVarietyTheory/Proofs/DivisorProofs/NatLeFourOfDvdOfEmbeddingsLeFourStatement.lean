import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatLeFourOfDvdOfEmbeddingsLeFour
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nat_le_four_of_dvd_of_embeddings_le_four' : ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ) (r : 𝓞 F), y ≠ 0 → y = m * r →
    (∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4) → m ≤ 4 := by
  first | exact @GlobalTheory.nat_le_four_of_dvd_of_embeddings_le_four | exact GlobalTheory.nat_le_four_of_dvd_of_embeddings_le_four | (intros; apply GlobalTheory.nat_le_four_of_dvd_of_embeddings_le_four <;> assumption)
