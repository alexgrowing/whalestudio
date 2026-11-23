import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementInSocle
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_complement_in_socle : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Set (Module.End ℂ V)) (N D P : Submodule ℂ V), N ≤ D → GlobalTheory.ThKLocSS.OpStable T N → GlobalTheory.ThKLocSS.socleOver T N D = D → N ≤ P → P ≤ D → GlobalTheory.ThKLocSS.OpStable T P → ∃ C : Submodule ℂ V, C ≤ D ∧ GlobalTheory.ThKLocSS.OpStable T C ∧ P ⊔ C = D ∧ P ⊓ C = N := by
  first | exact @GlobalTheory.ThKLocSS.exists_opStable_compl_of_socleOver_eq | exact GlobalTheory.ThKLocSS.exists_opStable_compl_of_socleOver_eq | (intros; apply GlobalTheory.ThKLocSS.exists_opStable_compl_of_socleOver_eq <;> assumption)
