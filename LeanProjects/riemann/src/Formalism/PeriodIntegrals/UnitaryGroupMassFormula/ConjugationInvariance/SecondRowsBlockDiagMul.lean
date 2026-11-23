import Mathlib
import Formalism.PeriodIntegrals.DatumConjInv

noncomputable section

open Matrix

namespace PI.DatumConjInvWork

variable {F : Type} [Field F] {a t : ℕ}

theorem firstRows_mul (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (g : Matrix (Fin a) (Fin a) F) :
    toRows₁ (x * g) = toRows₁ x * g := by
  ext i j
  rfl

theorem secondRows_mul (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) (g : Matrix (Fin a) (Fin a) F) :
    toRows₂ (x * g) = toRows₂ x * g := by
  ext i j
  rfl

theorem firstRows_blockDiag_mul (A : Matrix (Fin a) (Fin a) F) (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) :
    toRows₁ (fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) F) * x) = A * toRows₁ x := by
  ext i j
  simp [Matrix.toRows₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem secondRows_blockDiag_mul (A : Matrix (Fin a) (Fin a) F) (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) :
    toRows₂ (fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) F) * x) = toRows₂ x := by
  ext i j
  simp [Matrix.toRows₂, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem II_mul' (O : Subring F) (ϖ : F) (y : Matrix (Fin t) (Fin a) F)
    (hy : y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ) (g : Matrix (Fin a) (Fin a) F) (hg : ∀ i j, g i j ∈ O) :
    y * g ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by
  simp only [Formalism.DoubleCosetMeasures.IIset, Set.mem_setOf_eq] at hy ⊢
  intro i j
  choose o ho hyo using hy
  refine ⟨∑ k, o i k * g k j, Subring.sum_mem O fun k _ => O.mul_mem (ho i k) (hg k j), ?_⟩
  simp only [Matrix.mul_apply, hyo, Finset.mul_sum, mul_assoc]

theorem II_iff (O : Subring F) (ϖ : F) (k : GL (Fin a) F) (hk : k ∈ Formalism.DoubleCosetMeasures.GLint O a)
    (y : Matrix (Fin t) (Fin a) F) :
    y * (k : Matrix (Fin a) (Fin a) F) ∈ Formalism.DoubleCosetMeasures.IIset O ϖ ↔ y ∈ Formalism.DoubleCosetMeasures.IIset O ϖ := by
  have hk' : (∀ i j, (k : Matrix (Fin a) (Fin a) F) i j ∈ O) ∧
      (∀ i j, ((k⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j ∈ O) := hk
  constructor
  · intro h
    have h2 := II_mul' O ϖ _ h _ hk'.2
    rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h2
  · intro h
    exact II_mul' O ϖ y h _ hk'.1

private theorem int_mul_lemma {O : Subring F} {n : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) : ∀ i j, (A * B) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem O fun k _ => O.mul_mem (hA i k) (hB k j)

theorem conj_mem (O : Subring F) (ϖ : F) (h : GL (Fin a) F) (hh : h ∈ Formalism.DoubleCosetMeasures.GLint O a)
    (g : GL (Fin a) F) (hg : g ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a) :
    h⁻¹ * g * h ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a := by
  have hh' : (∀ i j, (h : Matrix (Fin a) (Fin a) F) i j ∈ O) ∧
      (∀ i j, ((h⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j ∈ O) := hh
  have hg' : g ∈ Formalism.DoubleCosetMeasures.GLint O a ∧
      ∀ i j, (ϖ⁻¹ • ((g : Matrix (Fin a) (Fin a) F) - 1)) i j ∈ O := hg
  have hmem : h⁻¹ * g * h ∈ Formalism.DoubleCosetMeasures.GLint O a :=
    (Formalism.DoubleCosetMeasures.GLint O a).mul_mem ((Formalism.DoubleCosetMeasures.GLint O a).mul_mem ((Formalism.DoubleCosetMeasures.GLint O a).inv_mem hh) hg'.1) hh
  have key : ϖ⁻¹ • (((h⁻¹ * g * h : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) - 1) =
      ((h⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * (ϖ⁻¹ • ((g : Matrix (Fin a) (Fin a) F) - 1)) *
        (h : Matrix (Fin a) (Fin a) F) := by
    simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul]
  show h⁻¹ * g * h ∈ Formalism.DoubleCosetMeasures.GLint O a ∧
    ∀ i j, (ϖ⁻¹ • (((h⁻¹ * g * h : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) - 1)) i j ∈ O
  refine ⟨hmem, ?_⟩
  rw [key]
  exact int_mul_lemma (int_mul_lemma hh'.2 hg'.2) hh'.1

theorem top_iff (O : Subring F) (ϖ : F) (k : GL (Fin a) F) (hk : k ∈ Formalism.DoubleCosetMeasures.GLint O a)
    (X : Matrix (Fin a) (Fin a) F) :
    (∃ g : Formalism.DoubleCosetMeasures.congSub O ϖ a, ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) =
        ((k⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) * X * (k : Matrix (Fin a) (Fin a) F)) ↔
      (∃ g : Formalism.DoubleCosetMeasures.congSub O ϖ a, ((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = X) := by
  constructor
  · rintro ⟨g, hg⟩
    have hm := conj_mem O ϖ k⁻¹ ((Formalism.DoubleCosetMeasures.GLint O a).inv_mem hk) (g : GL (Fin a) F) g.2
    refine ⟨⟨_, hm⟩, ?_⟩
    simp only [inv_inv, Units.val_mul, hg]
    simp [Matrix.mul_assoc]
  · rintro ⟨g, hg⟩
    have hm := conj_mem O ϖ k hk (g : GL (Fin a) F) g.2
    refine ⟨⟨_, hm⟩, ?_⟩
    simp [hg, Matrix.mul_assoc]

theorem main : PI.DatumConjInv := by
  unfold PI.DatumConjInv
  intro F _ O ϖ a t k hk x
  simp only [Formalism.DoubleCosetMeasures.phiU, MonoidHom.one_apply, Units.val_one]
  split_ifs with h1 h2 h2 <;> first
    | rfl
    | (exfalso
       rw [firstRows_mul, firstRows_blockDiag_mul, secondRows_mul, secondRows_blockDiag_mul, top_iff O ϖ k hk, II_iff O ϖ k hk] at h1
       exact h2 h1)
    | (exfalso
       rw [firstRows_mul, firstRows_blockDiag_mul, secondRows_mul, secondRows_blockDiag_mul, top_iff O ϖ k hk, II_iff O ϖ k hk] at h1
       exact h1 h2)

end PI.DatumConjInvWork
