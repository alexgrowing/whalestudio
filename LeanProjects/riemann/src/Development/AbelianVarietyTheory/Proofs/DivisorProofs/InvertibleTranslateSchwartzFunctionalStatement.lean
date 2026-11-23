import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvertibleTranslateSchwartzFunctional
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdQ
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invertible_translate_schwartz_functional : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) {a b : ℕ} (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ (P : Matrix (Fin (b + 2)) (Fin (b + 2)) (Fv F v)) (Q : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) (Fv F v)),
    IsUnit P.det → IsUnit Q.det →
    ∀ Λ : (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v) → ℂ) → ℂ,
    (∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)), ∀ g ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)),
      Λ (f + g) = Λ f + Λ g) →
    (∀ z : ℂ, ∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)), Λ (z • f) = z * Λ f) →
    (∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)), ∀ (r : Fin (a + (b + 2)) → Fv F v) (c : Fin b → Fv F v),
      Λ (fun Z => f (Z + P * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F v)) r c 0 * Q)) = Λ f) →
    (∀ U : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v),
      (∀ (r : Fin (a + (b + 2)) → Fv F v) (c : Fin b → Fv F v),
        ∑ i, ∑ j, U i j * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F v)) r c 0 i j = 0) →
      ∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)), ∀ f₁ ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)),
        (∀ Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v), f₁ (P * Z * Q) = ψ (∑ i, ∑ j, U i j * Z i j) * f (P * Z * Q)) → Λ f₁ = Λ f) →
    ∃ κ : ℂ, ∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)),
      Λ f = κ * ∫ r, ∫ c, f (P * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F v)) r c 0 * Q) ∂(haarVec v b) ∂(haarVec v (a + (b + 2))) := by
  first | exact @GlobalTheory.SBHaarDelta.main | exact GlobalTheory.SBHaarDelta.main | (intros; apply GlobalTheory.SBHaarDelta.main <;> assumption)
