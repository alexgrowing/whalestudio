import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzRedTil
import Development.DiscreteGroups.GlobalIrreducibility.DzRedSupp

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem corner_torusPow {m : ℕ} (d : Fin m → ℤ) :
    corner (Iwasawa.torusPow K m d) = Iwasawa.torusPow K (m + 1) (Fin.snoc d 0) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · rw [corner_last_last]; simp [Iwasawa.torusPow]
  · rw [corner_last_cs]; simp [Iwasawa.torusPow, Matrix.diagonal_apply, (Fin.castSucc_lt_last _).ne']
  · rw [corner_cs_last]; simp [Iwasawa.torusPow, Matrix.diagonal_apply, (Fin.castSucc_lt_last _).ne]
  · rw [corner_cs_cs]; simp [Iwasawa.torusPow, Matrix.diagonal_apply]

theorem longElt_mul_invT_torusPow {n : ℕ} (D : Fin n → ℤ) :
    longElt n K * GlobalTheory.CuspRep.invT n K (Iwasawa.torusPow K n D) =
      Iwasawa.torusPow K n (fun j => -D j.rev) * longElt n K := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [Units.val_mul, Units.val_mul, longElt_mul_apply, mul_longElt_apply, val_invT, ← Iwasawa.torusPow_neg]
  simp only [Matrix.transpose_apply, Iwasawa.torusPow, Iwasawa.coe_diagGL, Matrix.diagonal_apply, Pi.neg_apply]
  by_cases h : b = a.rev
  · subst h; simp
  · have h' : a ≠ b.rev := fun h' => h (by rw [h', Fin.rev_rev])
    simp [h, h']

theorem torusPow_const_comm {n : ℕ} (c : ℤ) (y : GL (Fin n) K) :
    Iwasawa.torusPow K n (fun _ => c) * y = y * Iwasawa.torusPow K n (fun _ => c) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  simp [Iwasawa.torusPow, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

theorem torusPow_zero' {n : ℕ} : Iwasawa.torusPow K n 0 = 1 := by
  show Iwasawa.diagGL K n (fun _ => _ ^ (0 : ℤ)) = 1
  simp only [zpow_zero]
  exact map_one _

theorem unipotent_le_unipB {n : ℕ} {u : GL (Fin n) K} (hu : u ∈ Iwasawa.unipotent K n) : u ∈ unipB K (Fin n) := by
  rw [Iwasawa.mem_unipotent] at hu
  exact (mem_unipB K).2 ⟨fun i j h => hu.1 h, hu.2⟩

end DiscreteGroups.sglob.DzRed
