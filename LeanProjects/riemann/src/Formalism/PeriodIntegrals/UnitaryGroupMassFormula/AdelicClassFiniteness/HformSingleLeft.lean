import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG
open scoped Matrix

section
variable {E : Type} [Field E] [StarRing E]

theorem cT_star {a b : Type} (A : Matrix a b E) : cT (starRingEnd E) A = Aᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply, starRingEnd_apply]

theorem isHerm_iff {n : Type} (J : Matrix n n E) : IsHerm (starRingEnd E) J ↔ Jᴴ = J := by
  unfold IsHerm
  rw [cT_star]

theorem hform_eq {n : Type} [Fintype n] (J : Matrix n n E) (x y : n → E) :
    hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  unfold hform
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem hform_mulVec {n a : Type} [Fintype n] [Fintype a] (J : Matrix n n E) (A B : Matrix n a E)
    (x y : a → E) :
    hform (starRingEnd E) J (A *ᵥ x) (B *ᵥ y) = hform (starRingEnd E) (cT (starRingEnd E) A * J * B) x y := by
  rw [hform_eq, hform_eq, cT_star, Matrix.star_mulVec]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

theorem hform_add_left {n : Type} [Fintype n] (J : Matrix n n E) (x x' y : n → E) :
    hform (starRingEnd E) J (x + x') y = hform (starRingEnd E) J x y + hform (starRingEnd E) J x' y := by
  simp [hform_eq, star_add, add_dotProduct]

theorem hform_single_left {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (i : n) (y : n → E) :
    hform (starRingEnd E) J (Pi.single i 1) y = (J *ᵥ y) i := by
  have hs : star (Pi.single i (1 : E) : n → E) = Pi.single i 1 := by
    ext r
    by_cases h : r = i
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [hform_eq, hs]
  simp

theorem hform_single {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (i j : n) :
    hform (starRingEnd E) J (Pi.single i 1) (Pi.single j 1) = J i j := by
  rw [hform_single_left]
  simp [Matrix.mulVec]

theorem cT_mulVec_apply {n k : Type} [Fintype n] (J : Matrix n n E) (V : Matrix n k E) (z : n → E) (i : k) :
    ((cT (starRingEnd E) V * J) *ᵥ z) i = hform (starRingEnd E) J (fun r => V r i) z := by
  rw [hform_eq, ← Matrix.mulVec_mulVec, cT_star]
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]

theorem gram_eq [NumberField E] {m k : ℕ} (J : Matrix (Fin m) (Fin m) E) (v : Fin k → Fin m → E) :
    gram J v = cT (starRingEnd E) (Matrix.of fun r i => v i r) * J * Matrix.of fun r i => v i r := by
  ext i j
  have h1 : (cT (starRingEnd E) (Matrix.of fun r i => v i r) * J * Matrix.of fun r i => v i r) i j =
      ((cT (starRingEnd E) (Matrix.of fun r i => v i r) * J) *ᵥ v j) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, cT_mulVec_apply]
  simp [PIW.AdelClassFin.gram]

end

end PIW.AdelClassFin
