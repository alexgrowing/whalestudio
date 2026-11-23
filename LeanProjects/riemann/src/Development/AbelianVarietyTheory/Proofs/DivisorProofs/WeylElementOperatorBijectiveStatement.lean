import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOpBOfMemClosure
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_element_operator_bijective : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChangeBij.HasOpB ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  first | exact @GlobalTheory.WeylBij.weyl_hasOpB | exact GlobalTheory.WeylBij.weyl_hasOpB | (intros; apply GlobalTheory.WeylBij.weyl_hasOpB <;> assumption)
