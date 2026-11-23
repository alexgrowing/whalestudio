import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_at_uniformizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E) (v : Pl F) (t : E →ₐ[F] Fv F v), UnrAt χ (splitPrime t) → chrW χ t (unifAt v) = val χ (splitPrime t) := by
  first | exact @GlobalTheory.ChrWUnif.chrW_unifAt | exact GlobalTheory.ChrWUnif.chrW_unifAt | (intros; apply GlobalTheory.ChrWUnif.chrW_unifAt <;> assumption)
