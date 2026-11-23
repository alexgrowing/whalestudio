import Mathlib

namespace GlobalTheory

open Subgroup

theorem relIndex_cocycle_of_ne_zero {A : Type} [Group A] (X Y Z : Subgroup A)
    (hXY : X.relIndex Y ≠ 0) (hYX : Y.relIndex X ≠ 0) (hYZ : Y.relIndex Z ≠ 0)
    (hZY : Z.relIndex Y ≠ 0) (hXZ : X.relIndex Z ≠ 0) (hZX : Z.relIndex X ≠ 0) :
    Y.relIndex X * Z.relIndex Y * X.relIndex Z = X.relIndex Y * Y.relIndex Z * Z.relIndex X := by
  have a1 := relIndex_inf_mul_relIndex Y Z X
  have a2 := relIndex_inf_mul_relIndex Z Y X
  have b1 := relIndex_inf_mul_relIndex Z X Y
  have b2 := relIndex_inf_mul_relIndex X Z Y
  have c1 := relIndex_inf_mul_relIndex X Y Z
  have c2 := relIndex_inf_mul_relIndex Y X Z
  rw [inf_comm Z Y] at a2
  rw [inf_comm Y X] at c2
  rw [inf_comm X Z] at b2
  rw [inf_comm Z Y] at b2
  rw [inf_comm Y X] at a2
  rw [inf_comm X Z] at c2
  have ha : (Y ⊓ Z).relIndex X ≠ 0 := relIndex_inf_ne_zero hYX hZX
  have hb : (Z ⊓ X).relIndex Y ≠ 0 := relIndex_inf_ne_zero hZY hXY
  have hc : (X ⊓ Y).relIndex Z ≠ 0 := relIndex_inf_ne_zero hXZ hYZ
  have hpY : Y.relIndex (Z ⊓ X) ≠ 0 := by
    intro h; apply ha; rw [← a1, h, zero_mul]
  have hpZ : Z.relIndex (X ⊓ Y) ≠ 0 := by
    intro h; apply hb; rw [← b1, h, zero_mul]
  have hpX : X.relIndex (Y ⊓ Z) ≠ 0 := by
    intro h; apply hc; rw [← c1, h, zero_mul]
  have hP : 0 < Z.relIndex (X ⊓ Y) * X.relIndex (Y ⊓ Z) * Y.relIndex (Z ⊓ X) := by
    positivity
  apply Nat.eq_of_mul_eq_mul_left hP
  calc Z.relIndex (X ⊓ Y) * X.relIndex (Y ⊓ Z) * Y.relIndex (Z ⊓ X) *
        (Y.relIndex X * Z.relIndex Y * X.relIndex Z)
      = (Z.relIndex (X ⊓ Y) * Y.relIndex X) * (X.relIndex (Y ⊓ Z) * Z.relIndex Y) *
        (Y.relIndex (Z ⊓ X) * X.relIndex Z) := by ring
    _ = (Y.relIndex (Z ⊓ X) * Z.relIndex X) * (Z.relIndex (X ⊓ Y) * X.relIndex Y) *
        (X.relIndex (Y ⊓ Z) * Y.relIndex Z) := by rw [a2, b2, c2, a1, b1, c1]
    _ = _ := by ring

theorem map_conj_mul {A : Type} [Group A] (K : Subgroup A) (x y : A) :
    K.map (MulAut.conj (x * y)).toMonoidHom =
      (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

theorem relIndex_map_conj {A : Type} [Group A] (H L : Subgroup A) (g : A) :
    (H.map (MulAut.conj g).toMonoidHom).relIndex (L.map (MulAut.conj g).toMonoidHom) =
      H.relIndex L :=
  Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

theorem map_conj_one {A : Type} [Group A] (K : Subgroup A) :
    K.map (MulAut.conj (1 : A)).toMonoidHom = K := by
  ext x; simp

theorem relIndex_conj_pow_succ {A : Type} [Group A] (K : Subgroup A) (g : A) (i : ℕ) :
    (K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom).relIndex
        (K.map (MulAut.conj (g ^ i)).toMonoidHom) =
      (K.map (MulAut.conj g).toMonoidHom).relIndex K ∧
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex
        (K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom) =
      K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  rw [pow_succ, map_conj_mul, relIndex_map_conj, relIndex_map_conj]
  exact ⟨rfl, rfl⟩

theorem relIndex_conj_pow_induction {A : Type} [Group A] (K : Subgroup A) (g : A)
    (ha : (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0)
    (hb : K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0) (i : ℕ) :
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex K ≠ 0 ∧
    K.relIndex (K.map (MulAut.conj (g ^ i)).toMonoidHom) ≠ 0 ∧
    (K.map (MulAut.conj (g ^ i)).toMonoidHom).relIndex K *
        (K.relIndex (K.map (MulAut.conj g).toMonoidHom)) ^ i =
      K.relIndex (K.map (MulAut.conj (g ^ i)).toMonoidHom) *
        ((K.map (MulAut.conj g).toMonoidHom).relIndex K) ^ i := by
  induction i with
  | zero =>
    rw [pow_zero, map_conj_one]
    simp
  | succ i ih =>
    obtain ⟨hu, hv, hi⟩ := ih
    obtain ⟨sa, sb⟩ := relIndex_conj_pow_succ K g i
    set B := K.map (MulAut.conj (g ^ i)).toMonoidHom
    set C := K.map (MulAut.conj (g ^ (i + 1))).toMonoidHom
    set a := (K.map (MulAut.conj g).toMonoidHom).relIndex K
    set b := K.relIndex (K.map (MulAut.conj g).toMonoidHom)
    have hCB : C.relIndex B ≠ 0 := by rw [sa]; exact ha
    have hBC : B.relIndex C ≠ 0 := by rw [sb]; exact hb
    have hCK : C.relIndex K ≠ 0 := relIndex_ne_zero_trans hCB hu
    have hKC : K.relIndex C ≠ 0 := relIndex_ne_zero_trans hv hBC
    have coc := relIndex_cocycle_of_ne_zero K B C hv hu hBC hCB hKC hCK
    rw [sa, sb] at coc
    refine ⟨hCK, hKC, ?_⟩
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hv)
    calc C.relIndex K * b ^ (i + 1) * K.relIndex B
        = b * K.relIndex B * C.relIndex K * b ^ i := by ring
      _ = B.relIndex K * a * K.relIndex C * b ^ i := by rw [coc]; ring
      _ = a * K.relIndex C * (B.relIndex K * b ^ i) := by ring
      _ = K.relIndex C * a ^ (i + 1) * K.relIndex B := by rw [hi]; ring

theorem relIndex_conj_eq_of_pow_eq : ∀ (A : Type) [Group A] (K : Subgroup A) (g : A) (n : ℕ), 0 < n →
    (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0 →
    K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0 →
    (K.map (MulAut.conj (g ^ n)).toMonoidHom).relIndex K =
      K.relIndex (K.map (MulAut.conj (g ^ n)).toMonoidHom) →
    (K.map (MulAut.conj g).toMonoidHom).relIndex K =
      K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  intro A _ K g n hn ha hb heq
  obtain ⟨hu, _, hi⟩ := relIndex_conj_pow_induction K g ha hb n
  rw [heq] at hi hu
  have hpow := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hu) hi
  exact (Nat.pow_left_injective (Nat.pos_iff_ne_zero.mp hn) hpow).symm

end GlobalTheory
