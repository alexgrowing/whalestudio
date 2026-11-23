import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdealCountLeOrder
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder

noncomputable section

open scoped TensorProduct NNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_ideal_count_le_order : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (x : (Fv F v ⊗[F] E)ˣ), (x : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v 𝔞 → ∀ w ∈ Formalism.L2.Host.aboveF (L := E) F v, FractionalIdeal.count E w 𝔞 ≤ GlobalTheory.UnrTate.ordAt v w x := by
  first | exact @GlobalTheory.UnrTate.count_le_ordAt_of_mem_locId | exact GlobalTheory.UnrTate.count_le_ordAt_of_mem_locId | (intros; apply GlobalTheory.UnrTate.count_le_ordAt_of_mem_locId <;> assumption)
