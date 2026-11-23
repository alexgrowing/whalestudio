import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveNormLeOne
open IsLocalRing

namespace GlobalTheory.PadicEmb

theorem exists_embedding : ∀ (p : ℕ) [Fact p.Prime] (D : Type) [CommRing D] [IsDomain D]
    [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D], (p : D) ≠ 0 →
    ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d, ‖φ d‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one
  | exact _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one
  | (apply _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one ..)

end GlobalTheory.PadicEmb
