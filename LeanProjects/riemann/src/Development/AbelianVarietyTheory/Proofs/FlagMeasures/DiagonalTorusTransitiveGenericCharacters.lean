import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Torus

theorem exists_mulShift {k : Type} [Field k] [Finite k] (ψ ψ' : AddChar k ℂ) (h : ψ ≠ 1) (h' : ψ' ≠ 1) :
    ∃ a : k, a ≠ 0 ∧ ψ' = ψ.mulShift a := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one h)
  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩
  obtain ⟨a, ha⟩ := hbij.2 ψ'
  refine ⟨a, ?_, ha.symm⟩
  rintro rfl
  exact h' (by rw [← ha, AddChar.mulShift_zero])

theorem conj_apply {k : Type} [Field k] {n : ℕ} (d : Fin n → kˣ) (M : Matrix (Fin n) (Fin n) k) (x y : Fin n) :
    (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1) : Matrix (Fin n) (Fin n) k) x y
      = (((d x)⁻¹ * d y : kˣ) : k) * M x y := by
  rw [mul_diagonal, diagonal_mul, Units.val_mul]
  ring

private lemma inJ_diagonal_conj_iff {k : Type} [Field k] {n t : ℕ} (d : Fin n → kˣ) (M : Matrix (Fin n) (Fin n) k) :
    InJ n t n false M ↔ InJ n t n false (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1)) := by
  have hc : ∀ x y : Fin n, (((d x)⁻¹ * d y : kˣ) : k) ≠ 0 := fun x y => Units.ne_zero _
  have h1 : ∀ x : Fin n, (((d x)⁻¹ * d x : kˣ) : k) = 1 := fun x => by
    rw [inv_mul_cancel, Units.val_one]
  simp only [InJ, conj_apply, mul_eq_zero, hc, false_or, Bool.false_eq_true, false_implies, and_true]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall_congr' fun x => imp_congr_right fun _ => ?_
    rw [h1, one_mul]
  · refine forall_congr' fun x => forall_congr' fun y => imp_congr_right fun _ => ?_
    split_ifs with hxy
    · subst hxy
      rw [h1, one_mul]
    · simp [hc]

private lemma inv_pow_mul_pow_succ_eq {k : Type} [Field k] (u : kˣ) (x y : ℕ) (h : x + 1 = y) :
    (((u ^ x)⁻¹ * u ^ y : kˣ) : k) = u := by
  subst h
  rw [pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]

theorem torus_transitive : ∀ (k : Type) [Field k] [Finite k] (n t : ℕ) (ψ ψ' : AddChar k ℂ) (χ χ' : ℕ → MulChar k ℂ), ψ ≠ 1 → ψ' ≠ 1 → ∃ d : Fin n → kˣ, ∀ M : Matrix (Fin n) (Fin n) k, (InJ n t n false M ↔ InJ n t n false (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1))) ∧ lamJ ψ' χ' n t 0 n M = (lamJ ψ χ n t 0 n (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1)))⁻¹ := by
  intro k _ _ n t ψ ψ' χ χ' hψ hψ'
  obtain ⟨a, ha, rfl⟩ := exists_mulShift ψ ψ' hψ hψ'
  set u : kˣ := Units.mk0 (-a) (neg_ne_zero.mpr ha) with hu
  refine ⟨fun i => u ^ (i : ℕ), fun M => ⟨inJ_diagonal_conj_iff _ M, ?_⟩⟩
  simp only [lamJ, conj_apply, Finset.prod_range_zero, mul_one, AddChar.mulShift_apply]
  rw [← AddChar.map_neg_eq_inv]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hxy
  · rw [inv_pow_mul_pow_succ_eq u _ _ hxy.1, hu, Units.val_mk0]
    ring
  · simp

end GlobalTheory.St.G.Torus
