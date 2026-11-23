import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCommonAlgClosedExtension

open scoped TensorProduct

namespace GlobalTheory

theorem exists_algClosed_join_of_two_field_extensions
    (K₀ K K' : Type) [Field K₀] [Field K] [Field K'] (i : K₀ →+* K) (i' : K₀ →+* K') :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (j : K →+* Ω) (j' : K' →+* Ω),
      j.comp i = j'.comp i' := by
  first
  | exact @_root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension
  | exact _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension
  | (apply _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension ..)

end GlobalTheory
