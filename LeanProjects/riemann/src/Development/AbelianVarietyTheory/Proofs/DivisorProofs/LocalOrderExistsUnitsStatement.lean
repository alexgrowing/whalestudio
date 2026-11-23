import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderExistsUnits
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder

noncomputable section

open scoped TensorProduct NNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_exists_units : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (k : HeightOneSpectrum (𝓞 E) → ℤ), ∃ x : (Fv F v ⊗[F] E)ˣ, ∀ w ∈ Formalism.L2.Host.aboveF (L := E) F v, GlobalTheory.UnrTate.ordAt v w x = k w := by
  first | exact @GlobalTheory.UnrTate.exists_unit_ordAt_eq | exact GlobalTheory.UnrTate.exists_unit_ordAt_eq | (intros; apply GlobalTheory.UnrTate.exists_unit_ordAt_eq <;> assumption)
