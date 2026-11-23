import Mathlib
import Formalism.PeriodIntegrals.TripleFrameDeterminant
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.LocalDet

noncomputable section

open NumberField

namespace PI.FlagFrameDeterminants

open Formalism.MainNotions.S

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}

theorem dl_eq_det (F : FlagG S r T) (F' : FlagG S r T') {j : ℕ} (hj : j ≤ r) :
    (Matrix.of fun a b : Fin j => S.hT (F.e (Fin.castLE hj a)) (F'.e (Fin.castLE hj b))).det =
      Dl F F' j := by
  have h1 : j ≤ r + 1 := by omega
  have key : ∀ a : Fin j, F.fvec (Fin.castLE h1 a) = F.e (Fin.castLE hj a) := fun a => by
    have hc : (Fin.castLE h1 a : Fin (r + 1)) = Fin.castSucc (Fin.castLE hj a) := Fin.ext rfl
    rw [hc]
    simp only [FlagG.fvec, Fin.snoc_castSucc]
  have key' : ∀ b : Fin j, F'.fvec (Fin.castLE h1 b) = F'.e (Fin.castLE hj b) := fun b => by
    have hc : (Fin.castLE h1 b : Fin (r + 1)) = Fin.castSucc (Fin.castLE hj b) := Fin.ext rfl
    rw [hc]
    simp only [FlagG.fvec, Fin.snoc_castSucc]
  unfold Dl leadMinorE
  rw [dif_pos h1]
  congr 1
  ext a b
  simp only [Matrix.of_apply, Matrix.submatrix_apply, Zhat, brS]
  rw [key a, key' b]

theorem frameExp_succ (r j : ℕ) : frameExp r (j + 1) = frameExp r j + (r - j) := by
  unfold frameExp
  rw [Finset.sum_Icc_succ_top (by omega)]
  omega

theorem prod_zpow_frame (N : ℝ) (hN : N ≠ 0) (r : ℕ) :
    ∀ j : ℕ, j ≤ r → ∏ a : Fin j, (N ^ (-((r : ℤ) - (a : ℕ)))) ^ 2 = N ^ (-(2 * (frameExp r j : ℤ)))
  | 0, _ => by simp [frameExp]
  | j + 1, hj => by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [prod_zpow_frame N hN r j (by omega), frameExp_succ]
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hN]
    congr 1
    push_cast [show j ≤ r by omega]
    ring

theorem nloc_eq (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hdd : dd ≠ 0) {r j : ℕ} (hj : j ≤ r) (x : E) :
    ((Nloc dd r j x : ℚ) : ℝ) = |((Algebra.norm ℚ x : ℚ) : ℝ)| *
      ∏ a : Fin j, ((FractionalIdeal.absNorm (dd ^ (-((r : ℤ) - (a : ℕ)))) : ℚ) : ℝ) ^ 2 := by
  have h0 : FractionalIdeal.absNorm dd ≠ 0 := by
    first
      | exact (map_ne_zero _).mpr hdd
      | exact FractionalIdeal.absNorm_eq_zero_iff.not.mpr hdd
  have hN : ((FractionalIdeal.absNorm dd : ℚ) : ℝ) ≠ 0 := by exact_mod_cast h0
  have hp := prod_zpow_frame ((FractionalIdeal.absNorm dd : ℚ) : ℝ) hN r j hj
  unfold Nloc
  simp only [map_mul, map_zpow₀, FractionalIdeal.absNorm_span_singleton]
  push_cast
  rw [hp]

end Gen

end PI.FlagFrameDeterminants
