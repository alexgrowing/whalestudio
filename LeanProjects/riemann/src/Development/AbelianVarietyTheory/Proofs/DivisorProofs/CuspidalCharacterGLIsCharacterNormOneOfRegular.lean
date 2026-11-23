import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterCuspidalRootSumRegular
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.GeneralLinearFunctionExtendZeroEndProperties

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem isChar_cusp_and_norm_of_reg (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (m k : ℕ) (hm : 0 < m)
    (hk : Reg (Nat.card F) m k) :
    IsChar ℂ ℂ (cusp θ m k) ∧
      ∑ᶠ x, cusp θ m k x * star (cusp θ m k x) = (Nat.card (GL (Fin m) F) : ℂ) := by
  obtain ⟨h1, h2⟩ := isChar_psi_rootSum_of_regular F θ hθ m k hm hk
  refine ⟨h1, ?_⟩
  have hip := ipGL_eq_finsum_GL (F := F) (d := m) (psi (rootSum θ k) (Fin m → F))
    (psi (rootSum θ k) (Fin m → F))
  rw [h2] at hip
  have hsq : ((-1 : ℂ) ^ (m - 1)) * star ((-1 : ℂ) ^ (m - 1)) = 1 := by
    rw [star_pow, star_neg, star_one, ← mul_pow]
    norm_num
  have hterm : ∀ x : GL (Fin m) F, cusp θ m k x * star (cusp θ m k x) =
      psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) *
        star (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))) := by
    intro x
    simp only [cusp, psiG, star_mul']
    linear_combination (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) *
        star (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)))) * hsq
  rw [finsum_congr hterm, ← hip]
  rfl

end GlobalTheory.Shin
