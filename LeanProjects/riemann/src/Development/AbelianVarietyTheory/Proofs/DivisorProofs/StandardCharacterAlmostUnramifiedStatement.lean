import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramified
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_character_almost_unramified : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) ∧ ∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1 := by
  first | exact @GlobalTheory.PsiStdCond.psi_std_conductor | exact GlobalTheory.PsiStdCond.psi_std_conductor | (intros; apply GlobalTheory.PsiStdCond.psi_std_conductor <;> assumption)
