import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => star (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.star_mem_schA_main | exact GlobalTheory.star_mem_schA_main | (intros; apply GlobalTheory.star_mem_schA_main <;> assumption)
