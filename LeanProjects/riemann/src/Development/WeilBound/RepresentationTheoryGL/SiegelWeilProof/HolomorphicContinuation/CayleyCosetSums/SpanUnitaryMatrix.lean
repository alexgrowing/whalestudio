import Mathlib

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

variable {n : ℕ}

theorem span_unitary_matrix :
    Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) = ⊤ := by
  open scoped Matrix.Norms.L2Operator in exact CStarAlgebra.span_unitary (A := Matrix (Fin n) (Fin n) ℂ)

theorem mem_unitary_of {U : Matrix (Fin n) (Fin n) ℂ} (h : Uᴴ * U = 1) : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
  ⟨h, mul_eq_one_comm.mp h⟩

def pm (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if σ i = j then 1 else 0

theorem pm_conj (σ : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) :
    pm σ * X * (pm σ)ᴴ = X.submatrix σ σ := by
  ext i j
  simp [pm, Matrix.mul_apply, Matrix.conjTranspose_apply, eq_comm]

theorem pm_unit (σ : Equiv.Perm (Fin n)) : (pm σ)ᴴ * pm σ = 1 := by
  ext i j
  simp only [pm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · by_cases h : i = j <;> simp [h, eq_comm, Equiv.apply_eq_iff_eq_symm_apply]
  · intro k _ hk
    have : σ k ≠ i := fun e => hk (by rw [← e]; simp)
    simp [this]
  · simp

def dph (a : Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if i = a then Complex.I else 1

theorem dph_unit (a : Fin n) : (dph a)ᴴ * dph a = 1 := by
  rw [dph, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i
  by_cases hi : i = a <;> simp [hi]

theorem dph_conj {a b : Fin n} (hab : a ≠ b) :
    dph a * Matrix.single a b (1 : ℂ) * (dph a)ᴴ = Complex.I • Matrix.single a b (1 : ℂ) := by
  ext i j
  rw [dph, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul, Pi.star_apply]
  by_cases hi : a = i <;> by_cases hj : b = j
  · subst hi hj; simp [hab.symm]
  · simp [hj]
  · simp [hi]
  · simp [hi, hj]

theorem inv_trace (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ U X : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → Xᴴ * X = 1 → L (U * X * Uᴴ) = L X) :
    ∀ X, L X = L 1 / n * X.trace := by

  have h' : ∀ U X : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → L (U * X * Uᴴ) = L X := by
    intro U X hU
    let C : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      L.comp ((LinearMap.mulLeft ℂ U).comp (LinearMap.mulRight ℂ Uᴴ)) - L
    have hC : Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set _) ≤ LinearMap.ker C := by
      rw [Submodule.span_le]
      intro Y hY
      have hY' : Yᴴ * Y = 1 := hY.1
      simp only [SetLike.mem_coe, LinearMap.mem_ker, C, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← Matrix.mul_assoc]
      rw [h U Y hU hY', sub_self]
    have hX : X ∈ LinearMap.ker C := hC (by rw [span_unitary_matrix]; trivial)
    simpa [C, sub_eq_zero, ← Matrix.mul_assoc] using hX

  have hoff : ∀ a b : Fin n, a ≠ b → L (Matrix.single a b 1) = 0 := by
    intro a b hab
    have e := h' (dph a) (Matrix.single a b 1) (dph_unit a)
    rw [dph_conj hab, L.map_smul, smul_eq_mul] at e
    have : (Complex.I - 1) * L (Matrix.single a b 1) = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (by simp [sub_eq_zero, Complex.ext_iff])
    · exact h0

  have hdiag : ∀ a b : Fin n, L (Matrix.single a a 1) = L (Matrix.single b b 1) := by
    intro a b
    have e := h' (pm (Equiv.swap a b)) (Matrix.single a a 1) (pm_unit _)
    rw [pm_conj] at e
    have : (Matrix.single a a (1 : ℂ)).submatrix (Equiv.swap a b) (Equiv.swap a b) = Matrix.single b b 1 := by
      have key : ∀ x, a = (Equiv.swap a b) x ↔ b = x := by
        intro x; rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, eq_comm]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.single_apply, key]
    rw [this] at e
    exact e.symm
  intro X
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : X = 0 := Subsingleton.elim _ _
    simp [this]
  set κ := L (Matrix.single (⟨0, hn⟩ : Fin n) ⟨0, hn⟩ 1)
  have hsum : ∀ Y : Matrix (Fin n) (Fin n) ℂ, L Y = κ * Y.trace := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [map_sum]
    rw [Matrix.trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [show Matrix.single a a (Y a a) = Y a a • Matrix.single a a (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
        L.map_smul, smul_eq_mul, hdiag a ⟨0, hn⟩, Matrix.diag_apply]; ring
    · intro b _ hb
      rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : ℂ) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
        L.map_smul, hoff a b (Ne.symm hb), smul_zero]
    · simp
  have h1 : L 1 = κ * n := by rw [hsum, trace_one, Fintype.card_fin]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hsum X, h1]; field_simp

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
