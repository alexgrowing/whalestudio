import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.UnitaryBorel

theorem borel_eq_diag_mul_unip_sameDiag : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (β : GU σ n), IsBorelU β →
    ∃ t ν : GU σ n, β = t * ν ∧ IsUnipU ν ∧
      (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) ∧
      ∀ i, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((β : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
  intro L _ _ σ n b hb
  obtain ⟨d, hd, hd'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ)
    (fun i => (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)
    (Formalism.UG.P.fSatake_unit_diag hb)
  have hne : ∀ i, (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i ≠ 0 :=
    Formalism.UG.P.fSatake_ne_zero_of_borel hb
  have hu : (((d⁻¹ * b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (fun i => ((((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i)⁻¹) *
        (((b : Formalism.UG.GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [Subgroup.coe_mul, Units.val_mul, hd']
  refine ⟨d, d⁻¹ * b, by group, ⟨fun i j hji => ?_, fun i => ?_⟩,
    fun i j hij => by rw [hd, Matrix.diagonal_apply_ne _ hij], fun i => by rw [hd, Matrix.diagonal_apply_eq]⟩
  · rw [hu, Matrix.diagonal_mul, hb i j hji, mul_zero]
  · rw [hu, Matrix.diagonal_mul, inv_mul_cancel₀ (hne i)]

end GlobalTheory.UnitaryBorel
