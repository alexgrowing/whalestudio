import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherLast
open IsLocalRing

namespace GlobalTheory

theorem finite_injective_localHom_and_extend (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R) :
    Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by
  first
  | exact @_root_.GlobalTheory.ValuationExtensionExistence.main
  | exact _root_.GlobalTheory.ValuationExtensionExistence.main
  | (apply _root_.GlobalTheory.ValuationExtensionExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationExtensionExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationExtensionExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationExtensionExistence.main ..)

end GlobalTheory
