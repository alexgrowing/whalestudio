import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.BZMir

section DerGroups

variable (k : Type) [Field k]

def colFix (N n : ℕ) : Subgroup (GL (Fin N) k) where
  carrier := {g | ∀ i : Fin N, (i : ℕ) < n →
    (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) = Pi.single i 1}
  mul_mem' {a b} ha hb := by
    intro i hi
    show ((a * b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec _ = _
    rw [Units.val_mul, ← mulVec_mulVec, hb i hi, ha i hi]
  one_mem' := by
    intro i _
    show ((1 : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec _ = _
    rw [Units.val_one, one_mulVec]
  inv_mem' {a} ha := by
    intro i hi
    show ((a⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec _ = _
    conv_lhs => rw [← ha i hi]
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]

def derUnip (N n : ℕ) : Subgroup (GL (Fin N) k) := unipB k (Fin N) ⊓ colFix k N n

theorem derUnip_le_unipB (N n : ℕ) : derUnip k N n ≤ unipB k (Fin N) := inf_le_left

theorem unipB_le_Mir (m : ℕ) : unipB k (Fin (m + 1)) ≤ Mir k m := by
  intro g hg
  obtain ⟨h1, h2⟩ := (mem_unipB k).1 hg
  rw [mem_Mir_iff]
  ext j
  by_cases hj : j = Fin.last m
  · subst hj
    simp [h2, eLast]
  · rw [h1 (Fin.last m) j (Fin.lt_last_iff_ne_last.2 hj)]
    simp [eLast, Pi.single_apply, hj]

theorem derUnip_le_Mir (m n : ℕ) : derUnip k (m + 1) n ≤ Mir k m :=
  (derUnip_le_unipB k (m + 1) n).trans (unipB_le_Mir k m)

def derUnipM (m n : ℕ) : Subgroup (Mir k m) := (derUnip k (m + 1) n).subgroupOf (Mir k m)

end DerGroups

section DerChars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def whitCharFrom (ψ : AddChar k Circle) (N n : ℕ) : unipB k (Fin N) →* ℂˣ where
  toFun u := Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ),
    (u : GL (Fin N) k).val p.1 p.2))
  map_one' := by
    rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
    intro p hp
    exact Matrix.one_apply_ne fun e => by have := (Finset.mem_filter.1 hp).2.1; rw [e] at this; omega
  map_mul' u v := by
    rw [← map_mul, ← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
    exact congrArg _ (congrArg _ (Finset.sum_congr rfl fun p hp => unipB_mul_apply u v (Finset.mem_filter.1 hp).2.1))

variable (k) in

def derChar (ψ : AddChar k Circle) (N n : ℕ) : derUnip k N n →* ℂˣ :=
  (whitCharFrom k ψ N n).comp (Subgroup.inclusion (derUnip_le_unipB k N n))

variable (k) in

def derCharM (ψ : AddChar k Circle) (m n : ℕ) : derUnipM k m n →* ℂˣ :=
  (derChar k ψ (m + 1) n).comp (Subgroup.subgroupOfEquivOfLe (derUnip_le_Mir k m n)).toMonoidHom

end DerChars

end GlobalTheory.BZMir

end
