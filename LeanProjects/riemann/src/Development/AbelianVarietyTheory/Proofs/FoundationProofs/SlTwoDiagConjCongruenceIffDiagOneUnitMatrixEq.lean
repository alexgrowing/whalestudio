import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNCong

theorem cong_iff_dg : ∀ (N : ℕ) (d : ℤ) (u : (ZMod N)ˣ), (u : ZMod N) = d → ∀ γ γ' : SL(2, ℤ),
    Cong N d γ γ' ↔ dg u * redGL N γ' = redGL N γ * dg u := by
  intro N d u hu γ γ'
  have key : (dg u * redGL N γ' = redGL N γ * dg u) ↔
      ((dg u : Matrix (Fin 2) (Fin 2) (ZMod N)) * (redGL N γ' : Matrix (Fin 2) (Fin 2) (ZMod N)) =
        (redGL N γ : Matrix (Fin 2) (Fin 2) (ZMod N)) * (dg u : Matrix (Fin 2) (Fin 2) (ZMod N))) := by
    constructor
    · intro h; rw [← Units.val_mul, h, Units.val_mul]
    · intro h; ext1; simpa using h
  rw [key]
  have hM : ∀ δ : SL(2, ℤ), (redGL N δ : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      !![(en δ 0 0 : ZMod N), en δ 0 1; en δ 1 0, en δ 1 1] := by
    intro δ
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hD : (dg u : Matrix (Fin 2) (Fin 2) (ZMod N)) = !![1, 0; 0, (d : ZMod N)] := by
    show !![1, 0; 0, (u : ZMod N)] = _
    rw [hu]
  rw [hM, hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [Cong, ← Matrix.ext_iff, Fin.forall_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, one_mul, zero_mul, add_zero,
    zero_add, mul_one, mul_zero]
  have hdu : IsUnit (d : ZMod N) := hu ▸ u.isUnit
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, ?_⟩, ?_, ?_⟩
    · rw [h2, mul_comm]
    · rw [h3]
    · rw [h4, mul_comm]
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h3, ?_⟩
    · rw [h2, mul_comm]
    · rw [mul_comm] at h4
      exact hdu.mul_right_cancel h4

end GlobalTheory.FNCong
