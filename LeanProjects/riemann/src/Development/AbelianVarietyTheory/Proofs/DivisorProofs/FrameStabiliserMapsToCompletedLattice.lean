import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
open NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem stab_hatL_mapsTo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Formalism.L2.DIV.IsFrame β Λ → ∀ x ∈ Formalism.L2.DIV.St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  intro hF x hx v hv
  obtain ⟨y, rfl⟩ := hx
  have hw := (hF v).1 hv
  refine (hF _).2 fun i => ?_
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map (Formalism.L2.Herm.intAf F E).subtype with hY
  have hval : ((Formalism.L2.DIV.frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) =
      (β : Matrix (Fin n) (Fin n) _) * Y * ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
    simp only [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Units.val_mul]
    rfl
  have hmv : ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (((Formalism.L2.DIV.frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ v) =
      Y *ᵥ (((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ v) := by
    rw [hval, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  rw [hmv]
  simp only [Matrix.mulVec, dotProduct]
  refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (hw j)
  simp only [hY, Matrix.map_apply]
  exact (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j |>.2

end GlobalTheory
