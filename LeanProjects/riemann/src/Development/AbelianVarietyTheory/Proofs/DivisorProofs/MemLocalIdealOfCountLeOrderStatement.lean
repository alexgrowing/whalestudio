import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalIdealOfCountLeOrder
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder

noncomputable section

open scoped TensorProduct NNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_local_ideal_of_count_le_order : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 → ∀ x : (Fv F v ⊗[F] E)ˣ, (∀ w ∈ Formalism.L2.Host.aboveF (L := E) F v, FractionalIdeal.count E w 𝔞 ≤ GlobalTheory.UnrTate.ordAt v w x) → (x : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞 := by
  first | exact @GlobalTheory.UnrTate.mem_locId_of_count_le_ordAt | exact GlobalTheory.UnrTate.mem_locId_of_count_le_ordAt | (intros; apply GlobalTheory.UnrTate.mem_locId_of_count_le_ordAt <;> assumption)
