import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitHomVal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.SplitCoord.UnipDual

open GlobalTheory.SmGL GlobalTheory.IndLineGL GlobalTheory.EmbChart

variable {R : Type} [Field R] {m : ℕ}

abbrev i0 (m : ℕ) : Ix m := ⟨0, (0 : Fin 1)⟩

abbrev i2 (m : ℕ) : Ix m := ⟨2, (0 : Fin 1)⟩

abbrev i1 {m : ℕ} (k : Fin m) : Ix m := ⟨1, k⟩

theorem sum_ix (f : Ix m → R) : ∑ x, f x = f (i0 m) + ∑ k : Fin m, f (i1 k) + f (i2 m) := by
  rw [Fintype.sum_sigma, Fin.sum_univ_three]
  congr 1
  · congr 1
    exact Fin.sum_univ_one (fun j : Fin 1 => f ⟨0, j⟩)
  · exact Fin.sum_univ_one (fun j : Fin 1 => f ⟨2, j⟩)

variable (K : Matrix (Fin m) (Fin m) R) (A : Matrix (Ix m) (Ix m) R)

theorem g02 : gamS K (i0 m) (i2 m) = 1 := rfl
theorem g20 : gamS K (i2 m) (i0 m) = -1 := rfl
theorem g11 (i j : Fin m) : gamS K (i1 i) (i1 j) = K i j := rfl
theorem g00 : gamS K (i0 m) (i0 m) = 0 := rfl
theorem g22 : gamS K (i2 m) (i2 m) = 0 := rfl
theorem g01 (j : Fin m) : gamS K (i0 m) (i1 j) = 0 := rfl
theorem g10 (j : Fin m) : gamS K (i1 j) (i0 m) = 0 := rfl
theorem g21 (j : Fin m) : gamS K (i2 m) (i1 j) = 0 := rfl
theorem g12 (j : Fin m) : gamS K (i1 j) (i2 m) = 0 := rfl

theorem left0 (y : Ix m) : (gamS K * A) (i0 m) y = A (i2 m) y := by
  rw [Matrix.mul_apply, sum_ix]; simp only [g02, g20, g11, g00, g22, g01, g10, g21, g12]; simp
theorem left2 (y : Ix m) : (gamS K * A) (i2 m) y = - A (i0 m) y := by
  rw [Matrix.mul_apply, sum_ix]; simp only [g02, g20, g11, g00, g22, g01, g10, g21, g12]; simp
theorem left1 (i : Fin m) (y : Ix m) : (gamS K * A) (i1 i) y = ∑ k, K i k * A (i1 k) y := by
  rw [Matrix.mul_apply, sum_ix]; simp only [g02, g20, g11, g00, g22, g01, g10, g21, g12]; simp
theorem right0 (x : Ix m) : (A * gamS K) x (i0 m) = - A x (i2 m) := by
  rw [Matrix.mul_apply, sum_ix]; simp only [g02, g20, g11, g00, g22, g01, g10, g21, g12]; simp
theorem right2 (x : Ix m) : (A * gamS K) x (i2 m) = A x (i0 m) := by
  rw [Matrix.mul_apply, sum_ix]; simp only [g02, g20, g11, g00, g22, g01, g10, g21, g12]; simp
theorem right1 (x : Ix m) (j : Fin m) : (A * gamS K) x (i1 j) = ∑ k, A x (i1 k) * K k j := by
  rw [Matrix.mul_apply, sum_ix]; simp only [g02, g20, g11, g00, g22, g01, g10, g21, g12]; simp

theorem unipRad_dual (R : Type) [Field R] (m n : ℕ) (e : GlobalTheory.SplitCoord.Ix m ≃ Fin n) (K : GL (Fin m) R)
    (N N' : GL (Fin n) R) (hN : N ∈ GlobalTheory.SmGL.unipRad R e)
    (h : (N : Matrix (Fin n) (Fin n) R)ᵀ * GlobalTheory.SplitCoord.gam e (K : Matrix (Fin m) (Fin m) R) *
      (N' : Matrix (Fin n) (Fin n) R) = GlobalTheory.SplitCoord.gam e (K : Matrix (Fin m) (Fin m) R)) :
    N' ∈ GlobalTheory.SmGL.unipRad R e := by
  obtain ⟨hp, hd⟩ := mem_unipRad.1 (inv_mem hN)
  rw [mem_parab_iff] at hp
  set M : Matrix (Fin n) (Fin n) R := ((N⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hM
  have h1 : gam e (K : Matrix (Fin m) (Fin m) R) * (N' : Matrix (Fin n) (Fin n) R) =
      Mᵀ * gam e (K : Matrix (Fin m) (Fin m) R) := by
    conv_rhs => rw [← h]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, ← Matrix.transpose_mul, hM, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.transpose_one, Matrix.one_mul]
  set A : Matrix (Ix m) (Ix m) R := (N' : Matrix (Fin n) (Fin n) R).submatrix e e with hA
  set C : Matrix (Ix m) (Ix m) R := Mᵀ.submatrix e e with hC
  have hg : (gam e (K : Matrix (Fin m) (Fin m) R)).submatrix e e = gamS (K : Matrix (Fin m) (Fin m) R) := by
    ext x y; simp [gam]
  have h2 : gamS (K : Matrix (Fin m) (Fin m) R) * A = C * gamS (K : Matrix (Fin m) (Fin m) R) := by
    rw [← hg, hA, hC, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h1]
  have c00 : C (i0 m) (i0 m) = 1 := (hd 0 (0 : Fin 1) (0 : Fin 1)).trans (Matrix.one_apply_eq _)
  have c22 : C (i2 m) (i2 m) = 1 := (hd 2 (0 : Fin 1) (0 : Fin 1)).trans (Matrix.one_apply_eq _)
  have c11 : ∀ i j : Fin m, C (i1 i) (i1 j) = (1 : Matrix (Fin m) (Fin m) R) i j := fun i j =>
    (hd 1 j i).trans (by
      show (1 : Matrix (Fin m) (Fin m) R) j i = _
      simp [Matrix.one_apply, eq_comm])
  have c02 : C (i0 m) (i2 m) = 0 := hp 2 0 (0 : Fin 1) (0 : Fin 1) (by decide)
  have c01 : ∀ j : Fin m, C (i0 m) (i1 j) = 0 := fun j => hp 1 0 j (0 : Fin 1) (by decide)
  have c12 : ∀ j : Fin m, C (i1 j) (i2 m) = 0 := fun j => hp 2 1 (0 : Fin 1) j (by decide)
  have a00 : A (i0 m) (i0 m) = 1 := by
    have := congrFun (congrFun h2 (i2 m)) (i0 m)
    rw [left2, right0, c22] at this
    exact neg_injective this
  have a22 : A (i2 m) (i2 m) = 1 := by
    have := congrFun (congrFun h2 (i0 m)) (i2 m)
    rwa [left0, right2, c00] at this
  have a20 : A (i2 m) (i0 m) = 0 := by
    have := congrFun (congrFun h2 (i0 m)) (i0 m)
    rwa [left0, right0, c02, neg_zero] at this
  have a21 : ∀ j : Fin m, A (i2 m) (i1 j) = 0 := fun j => by
    have := congrFun (congrFun h2 (i0 m)) (i1 j)
    rw [left0, right1] at this
    simpa [c01] using this
  have a10 : ∀ j : Fin m, A (i1 j) (i0 m) = 0 := by
    have hv : (K : Matrix (Fin m) (Fin m) R) * (Matrix.of fun k (_ : Fin m) => A (i1 k) (i0 m)) = 0 := by
      ext i j
      have := congrFun (congrFun h2 (i1 i)) (i0 m)
      rw [left1, right0, c12, neg_zero] at this
      exact this
    have := (Units.mul_right_eq_zero K).1 hv
    exact fun j => congrFun (congrFun this j) j
  have a11 : ∀ i j : Fin m, A (i1 i) (i1 j) = (1 : Matrix (Fin m) (Fin m) R) i j := by
    have hv : (K : Matrix (Fin m) (Fin m) R) * (Matrix.of fun k j => A (i1 k) (i1 j)) = K * 1 := by
      ext i j
      have := congrFun (congrFun h2 (i1 i)) (i1 j)
      rw [left1, right1] at this
      refine this.trans ?_
      simp only [c11]
      rw [Matrix.mul_one, ← Matrix.mul_apply, Matrix.one_mul]
    have := (Units.mul_right_inj K).1 hv
    exact fun i j => congrFun (congrFun this i) j
  have fin1 : ∀ i : Fin 1, i = 0 := fun i => Subsingleton.elim _ _
  refine mem_unipRad.2 ⟨mem_parab_iff.2 ?_, ?_⟩
  · intro a b i j hab
    fin_cases a <;> fin_cases b <;> try exact absurd hab (by decide)
    · obtain rfl := fin1 j
      exact a10 i
    · obtain rfl := fin1 i
      obtain rfl := fin1 j
      exact a20
    · obtain rfl := fin1 i
      exact a21 j
  · intro a i j
    fin_cases a
    · obtain rfl := fin1 i
      obtain rfl := fin1 j
      exact a00.trans (Matrix.one_apply_eq _).symm
    · exact a11 i j
    · obtain rfl := fin1 i
      obtain rfl := fin1 j
      exact a22.trans (Matrix.one_apply_eq _).symm

end GlobalTheory.SplitCoord.UnipDual
