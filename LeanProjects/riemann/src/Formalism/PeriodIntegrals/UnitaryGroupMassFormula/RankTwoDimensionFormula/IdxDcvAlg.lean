import Mathlib
import Formalism.SatakeDualWeyl.Statement

open Matrix

namespace PI.UnitaryDimensionFormula.FrameAlg

variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)

theorem h_add_right (x y y' : n → A) :
    Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem h_smul_right (x y : n → A) (a : A) :
    Formalism.UG.hform σ J x (a • y) = a * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem h_sub_right (x y y' : n → A) :
    Formalism.UG.hform σ J x (y - y') = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem h_zero_right (x : n → A) : Formalism.UG.hform σ J x 0 = 0 := by
  simp [Formalism.UG.hform]

theorem h_sum_right {ι : Type} (s : Finset ι) (x : n → A) (v : ι → n → A) :
    Formalism.UG.hform σ J x (∑ l ∈ s, v l) = ∑ l ∈ s, Formalism.UG.hform σ J x (v l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_right, ih]

theorem h_add_left (x x' y : n → A) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem h_smul_left (x y : n → A) (a : A) :
    Formalism.UG.hform σ J (a • x) y = σ a * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem h_zero_left (y : n → A) : Formalism.UG.hform σ J 0 y = 0 := by
  simp [Formalism.UG.hform]

theorem h_sum_left {ι : Type} (s : Finset ι) (v : ι → n → A) (y : n → A) :
    Formalism.UG.hform σ J (∑ l ∈ s, v l) y = ∑ l ∈ s, Formalism.UG.hform σ J (v l) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h_add_left, ih]

theorem h_symm (hJ : Formalism.UG.cT σ J = J) (hσ : ∀ a, σ (σ a) = a) (x y : n → A) :
    Formalism.UG.hform σ J y x = σ (Formalism.UG.hform σ J x y) := by
  have hJ' : ∀ i j, J i j = σ (J j i) := fun i j => by
    have h := congrFun (congrFun hJ i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at h
    exact h.symm
  simp only [Formalism.UG.hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ' j i]
  ring

variable {r : ℕ}

def Q (e f : Fin r → n → A) (z y : n → A) : n → A :=
  (-Formalism.UG.hform σ J z z) • (y - ∑ a, (Formalism.UG.hform σ J (f a) y • e a + Formalism.UG.hform σ J (e a) y • f a)) +
    Formalism.UG.hform σ J z y • z

structure Hyp (e f : Fin r → n → A) (z : n → A) : Prop where
  ee : ∀ a b, Formalism.UG.hform σ J (e a) (e b) = 0
  ff : ∀ a b, Formalism.UG.hform σ J (f a) (f b) = 0
  ef : ∀ a b, Formalism.UG.hform σ J (e a) (f b) = if a = b then 1 else 0
  ez : ∀ a, Formalism.UG.hform σ J (e a) z = 0
  fz : ∀ a, Formalism.UG.hform σ J (f a) z = 0

private theorem Q_eq_hform_expansion (e f : Fin r → n → A) (z y w : n → A) :
    Formalism.UG.hform σ J w (Q σ J e f z y) =
      -Formalism.UG.hform σ J z z * (Formalism.UG.hform σ J w y - ∑ a, (Formalism.UG.hform σ J (f a) y * Formalism.UG.hform σ J w (e a) +
        Formalism.UG.hform σ J (e a) y * Formalism.UG.hform σ J w (f a))) + Formalism.UG.hform σ J z y * Formalism.UG.hform σ J w z := by
  simp only [Q, h_add_right, h_smul_right, h_sub_right, h_sum_right]

theorem dual_fix (hσ : ∀ a, σ (σ a) = a) {k : ℕ} (b c : Fin k → n → A) (ε : A) (M : Matrix (Fin k) (Fin k) A)
    (hM : M * Matrix.of (fun l j => Formalism.UG.hform σ J (c l) (b j)) = ε • (1 : Matrix (Fin k) (Fin k) A))
    (i j : Fin k) :
    Formalism.UG.hform σ J (∑ l, σ (M i l) • c l) (b j) = if i = j then ε else 0 := by
  have h := congrFun (congrFun hM i) j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  rw [h_sum_left]
  simp only [h_smul_left, hσ]
  rw [h]
  split_ifs <;> simp

theorem inv_on {k : ℕ} (G : Matrix (Fin k) (Fin k) A) (ε y : A) (hy : ε * G.det * y = ε) :
    ((ε * y) • G.adjugate) * G = ε • (1 : Matrix (Fin k) (Fin k) A) := by
  rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
  congr 1
  linear_combination hy

theorem Q_perp_idem (hJ : Formalism.UG.cT σ J = J) (hσ : ∀ a, σ (σ a) = a) {e f : Fin r → n → A} {z : n → A} (E₁ : A)
    (hE : E₁ * E₁ = E₁) (hEs : σ E₁ = E₁) (he : ∀ a, e a = E₁ • e a) (hf : ∀ a, f a = E₁ • f a)
    (hee : ∀ a b, Formalism.UG.hform σ J (e a) (e b) = 0) (hff : ∀ a b, Formalism.UG.hform σ J (f a) (f b) = 0)
    (hef : ∀ a b, Formalism.UG.hform σ J (e a) (f b) = if a = b then E₁ else 0)
    (hez : ∀ a, Formalism.UG.hform σ J (e a) z = 0) (hfz : ∀ a, Formalism.UG.hform σ J (f a) z = 0) (y : n → A) :
    (∀ b, Formalism.UG.hform σ J (e b) (Q σ J e f z y) = 0) ∧ (∀ b, Formalism.UG.hform σ J (f b) (Q σ J e f z y) = 0) ∧
      Formalism.UG.hform σ J z (Q σ J e f z y) = 0 := by
  have hfe : ∀ a b, Formalism.UG.hform σ J (f b) (e a) = if a = b then E₁ else 0 := fun a b => by
    rw [h_symm σ J hJ hσ (e a) (f b), hef]; split_ifs <;> simp [hEs]
  have hze : ∀ a, Formalism.UG.hform σ J z (e a) = 0 := fun a => by rw [h_symm σ J hJ hσ (e a) z, hez, map_zero]
  have hzf : ∀ a, Formalism.UG.hform σ J z (f a) = 0 := fun a => by rw [h_symm σ J hJ hσ (f a) z, hfz, map_zero]
  have hEe : ∀ b, Formalism.UG.hform σ J (e b) y = Formalism.UG.hform σ J (e b) y * E₁ := fun b => by
    conv_lhs => rw [he b, h_smul_left, hEs]
    ring
  have hEf : ∀ b, Formalism.UG.hform σ J (f b) y = Formalism.UG.hform σ J (f b) y * E₁ := fun b => by
    conv_lhs => rw [hf b, h_smul_left, hEs]
    ring
  refine ⟨fun b => ?_, fun b => ?_, ?_⟩ <;> rw [Q_eq_hform_expansion]
  · simp [hee, hef, hez]
    rw [← hEe b]; ring
  · simp [hfe, hff, hfz]
    rw [← hEf b]; ring
  · simp [hze, hzf]; ring

end PI.UnitaryDimensionFormula.FrameAlg
