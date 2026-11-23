import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translationInvariant_doubledForm_conjProduct_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Ψ ∈ schA F κ, Ψ ≠ 0 →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ φ ∈ schA F (κ ⊕ κ), ∀ (φ' : (κ ⊕ κ → AF F) → ℂ) (x : κ → AF F),
      (∀ u, φ' (Sum.elim u u) = φ (Sum.elim (u + x) (u + x))) → l φ' = l φ) ∧ l (GlobalTheory.InertDbl.dblFun Ψ) ≠ 0 := by
  first | exact @GlobalTheory.DblDiagForm.exists_form | exact GlobalTheory.DblDiagForm.exists_form | (intros; apply GlobalTheory.DblDiagForm.exists_form <;> assumption)
