import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.ContDiffOnExpPartialHomeomorphSymm

namespace CompanionTheory.D.Upq

open Matrix

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

section Generic

variable (J : Matrix n n ℂ)

def lieJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | Xᴴ * J + J * X = 0}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq, conjTranspose_add, Matrix.add_mul, Matrix.mul_add] at hX hY ⊢
    calc Xᴴ * J + Yᴴ * J + (J * X + J * Y) = (Xᴴ * J + J * X) + (Yᴴ * J + J * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [Set.mem_ofPred_eq, conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul] at hX ⊢
    rw [← smul_add, hX, smul_zero]

theorem mem_lieJ {X : Matrix n n ℂ} : X ∈ lieJ J ↔ Xᴴ * J + J * X = 0 := Iff.rfl

variable {J}

theorem conjTranspose_mul_eq_of_mem {X : Matrix n n ℂ} (hX : X ∈ lieJ J) : Xᴴ * J = -(J * X) :=
  eq_neg_of_add_eq_zero_left hX

theorem commutator_mem_lieJ {X Y : Matrix n n ℂ} (hX : X ∈ lieJ J) (hY : Y ∈ lieJ J) :
    X * Y - Y * X ∈ lieJ J := by
  have hX' := conjTranspose_mul_eq_of_mem hX
  have hY' := conjTranspose_mul_eq_of_mem hY
  show (X * Y - Y * X)ᴴ * J + J * (X * Y - Y * X) = 0
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul,
    Matrix.mul_assoc Yᴴ Xᴴ J, hX', Matrix.mul_assoc Xᴴ Yᴴ J, hY', Matrix.mul_neg, Matrix.mul_neg,
    ← Matrix.mul_assoc Yᴴ J X, hY', ← Matrix.mul_assoc Xᴴ J Y, hX']
  simp only [Matrix.neg_mul, neg_neg, Matrix.mul_sub, Matrix.mul_assoc]
  abel

variable (J) in

def lieSubJ : LieSubalgebra ℝ (Matrix n n ℂ) :=
  { lieJ J with
    lie_mem' := fun {X Y} hX hY => by
      rw [Ring.lie_def]
      exact commutator_mem_lieJ hX hY }

@[simp] theorem mem_lieSubJ {X : Matrix n n ℂ} : X ∈ lieSubJ J ↔ X ∈ lieJ J := Iff.rfl

theorem lie_mem_lieSubJ {X Y : Matrix n n ℂ} (hX : X ∈ lieSubJ J) (hY : Y ∈ lieSubJ J) :
    ⁅X, Y⁆ ∈ lieSubJ J :=
  (lieSubJ J).lie_mem hX hY

end Generic

section Involutive

variable {J : Matrix n n ℂ} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ

theorem mul_J_J (Z : Matrix n n ℂ) : Z * J * J = Z := by
  rw [Matrix.mul_assoc, hJ, Matrix.mul_one]

theorem J_J_mul (Z : Matrix n n ℂ) : J * (J * Z) = Z := by
  rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]

theorem mem_lieJ_iff {X : Matrix n n ℂ} : X ∈ lieJ J ↔ Xᴴ = -(J * X * J) := by
  constructor
  · intro h
    calc Xᴴ = Xᴴ * J * J := (mul_J_J hJ _).symm
      _ = -(J * X * J) := by rw [conjTranspose_mul_eq_of_mem h, Matrix.neg_mul]
  · intro h
    show Xᴴ * J + J * X = 0
    rw [h, Matrix.neg_mul, mul_J_J hJ, neg_add_cancel]

theorem conjTranspose_mem_lieJ {X : Matrix n n ℂ} (hX : X ∈ lieJ J) : Xᴴ ∈ lieJ J := by
  rw [mem_lieJ_iff hJ] at hX ⊢
  rw [conjTranspose_conjTranspose, hX]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul,
    mul_J_J hJ]

theorem J_mul_mul_J_of_mem {X : Matrix n n ℂ} (hX : X ∈ lieJ J) : J * X * J = -Xᴴ := by
  rw [(mem_lieJ_iff hJ).1 hX, neg_neg]

theorem J_mul_mul_J_mem {X : Matrix n n ℂ} (hX : X ∈ lieJ J) : J * X * J ∈ lieJ J := by
  rw [J_mul_mul_J_of_mem hJ hX]
  exact neg_mem (conjTranspose_mem_lieJ hJ hX)

end Involutive

section Cartan

variable (J : Matrix n n ℂ)

def kJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | X ∈ lieJ J ∧ X * J = J * X}
  add_mem' {X Y} hX hY := ⟨add_mem hX.1 hY.1, by rw [Matrix.add_mul, Matrix.mul_add, hX.2, hY.2]⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' c X hX := ⟨Submodule.smul_mem _ c hX.1, by
    rw [Matrix.smul_mul, Matrix.mul_smul, hX.2]⟩

def pJ : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | X ∈ lieJ J ∧ X * J = -(J * X)}
  add_mem' {X Y} hX hY := ⟨add_mem hX.1 hY.1, by
    rw [Matrix.add_mul, Matrix.mul_add, hX.2, hY.2, neg_add]⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  smul_mem' c X hX := ⟨Submodule.smul_mem _ c hX.1, by
    rw [Matrix.smul_mul, Matrix.mul_smul, hX.2, smul_neg]⟩

theorem mem_kJ {X : Matrix n n ℂ} : X ∈ kJ J ↔ X ∈ lieJ J ∧ X * J = J * X := Iff.rfl

theorem mem_pJ {X : Matrix n n ℂ} : X ∈ pJ J ↔ X ∈ lieJ J ∧ X * J = -(J * X) := Iff.rfl

theorem kJ_le : kJ J ≤ lieJ J := fun _ h => h.1

theorem pJ_le : pJ J ≤ lieJ J := fun _ h => h.1

variable {J} (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ

theorem mem_kJ_iff {X : Matrix n n ℂ} : X ∈ kJ J ↔ X ∈ lieJ J ∧ Xᴴ = -X := by
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · rw [(mem_lieJ_iff hJ).1 h.1, h.2.symm, mul_J_J hJ]
  · have e := J_mul_mul_J_of_mem hJ h.1
    rw [h.2, neg_neg] at e
    calc X * J = J * (J * X * J) := by
          rw [← Matrix.mul_assoc J (J * X) J, ← Matrix.mul_assoc J J X, hJ, Matrix.one_mul]
      _ = J * X := by rw [e]

theorem mem_pJ_iff {X : Matrix n n ℂ} : X ∈ pJ J ↔ X ∈ lieJ J ∧ Xᴴ = X := by
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · rw [(mem_lieJ_iff hJ).1 h.1, Matrix.mul_assoc J X J, h.2, Matrix.mul_neg, neg_neg,
      ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  · have e := J_mul_mul_J_of_mem hJ h.1
    rw [h.2] at e
    calc X * J = J * (J * X * J) := by
          rw [← Matrix.mul_assoc J (J * X) J, ← Matrix.mul_assoc J J X, hJ, Matrix.one_mul]
      _ = -(J * X) := by rw [e, Matrix.mul_neg]

theorem kJ_inf_pJ : kJ J ⊓ pJ J = ⊥ := by
  rw [eq_bot_iff]
  rintro X ⟨hK, hP⟩
  rw [Submodule.mem_bot]
  have h1 : J * X = -(J * X) := hK.2.symm.trans hP.2
  have h2 : J * X = 0 := by
    have : (2 : ℂ) • (J * X) = 0 := by rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel _
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  rw [← J_J_mul hJ X, h2, Matrix.mul_zero]

theorem kJ_sup_pJ : kJ J ⊔ pJ J = lieJ J := by
  refine le_antisymm (sup_le (kJ_le J) (pJ_le J)) fun X hX => ?_
  have hX' := J_mul_mul_J_mem hJ hX
  refine Submodule.mem_sup.2 ⟨(1 / 2 : ℝ) • (X + J * X * J), ⟨Submodule.smul_mem _ _ (add_mem hX hX'), ?_⟩,
    (1 / 2 : ℝ) • (X - J * X * J), ⟨Submodule.smul_mem _ _ (sub_mem hX hX'), ?_⟩, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, mul_J_J hJ,
      ← Matrix.mul_assoc J (J * X) J, ← Matrix.mul_assoc J J X, hJ, Matrix.one_mul, add_comm (J * X)]
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, mul_J_J hJ,
      ← Matrix.mul_assoc J (J * X) J, ← Matrix.mul_assoc J J X, hJ, Matrix.one_mul, ← smul_neg, neg_sub]
  · rw [← smul_add, add_add_sub_cancel, ← two_smul ℝ X, smul_smul]
    norm_num

theorem commutator_mem_kJ {X Y : Matrix n n ℂ} (hX : X ∈ kJ J) (hY : Y ∈ kJ J) :
    X * Y - Y * X ∈ kJ J :=
  ⟨commutator_mem_lieJ hX.1 hY.1, by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc X Y J, hY.2, ← Matrix.mul_assoc X J Y, hX.2,
      Matrix.mul_assoc Y X J, hX.2, ← Matrix.mul_assoc Y J X, hY.2, Matrix.mul_assoc J X Y,
      Matrix.mul_assoc J Y X]⟩

theorem commutator_mem_pJ {X Y : Matrix n n ℂ} (hX : X ∈ kJ J) (hY : Y ∈ pJ J) :
    X * Y - Y * X ∈ pJ J :=
  ⟨commutator_mem_lieJ hX.1 hY.1, by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc X Y J, hY.2, Matrix.mul_neg,
      ← Matrix.mul_assoc X J Y, hX.2, Matrix.mul_assoc Y X J, hX.2, ← Matrix.mul_assoc Y J X, hY.2,
      Matrix.neg_mul, Matrix.mul_assoc J X Y, Matrix.mul_assoc J Y X, neg_sub_neg, neg_sub]⟩

theorem commutator_mem_kJ_of_pJ {X Y : Matrix n n ℂ} (hX : X ∈ pJ J) (hY : Y ∈ pJ J) :
    X * Y - Y * X ∈ kJ J :=
  ⟨commutator_mem_lieJ hX.1 hY.1, by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc X Y J, hY.2, Matrix.mul_neg,
      ← Matrix.mul_assoc X J Y, hX.2, Matrix.neg_mul, neg_neg, Matrix.mul_assoc Y X J, hX.2,
      Matrix.mul_neg, ← Matrix.mul_assoc Y J X, hY.2, Matrix.neg_mul, neg_neg, Matrix.mul_assoc J X Y,
      Matrix.mul_assoc J Y X]⟩

end Cartan

section Complexification

variable (J : Matrix n n ℂ)

def thetaG (M : Matrix n n ℂ) : Matrix n n ℂ := -(J * Mᴴ * J)

noncomputable def reG (M : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℂ) • (M + thetaG J M)

noncomputable def imG (M : Matrix n n ℂ) : Matrix n n ℂ := (-(Complex.I / 2)) • (M - thetaG J M)

variable {J}

theorem thetaG_add (M N : Matrix n n ℂ) : thetaG J (M + N) = thetaG J M + thetaG J N := by
  simp only [thetaG, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, neg_add]

theorem thetaG_sub (M N : Matrix n n ℂ) : thetaG J (M - N) = thetaG J M - thetaG J N := by
  simp only [thetaG, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, neg_sub_neg, neg_sub]

theorem thetaG_smul (c : ℂ) (M : Matrix n n ℂ) : thetaG J (c • M) = star c • thetaG J M := by
  simp only [thetaG, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

variable (hJ : J * J = 1) (hJh : Jᴴ = J)
include hJ hJh

theorem thetaG_thetaG (M : Matrix n n ℂ) : thetaG J (thetaG J M) = M := by
  simp only [thetaG, conjTranspose_neg, conjTranspose_mul, hJh, conjTranspose_conjTranspose,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul, mul_J_J hJ]

omit hJh in

theorem mem_lieJ_iff_thetaG {X : Matrix n n ℂ} : X ∈ lieJ J ↔ thetaG J X = X := by
  rw [mem_lieJ_iff hJ, thetaG]
  constructor
  · intro h
    rw [h]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul,
      mul_J_J hJ]
  · intro h
    calc Xᴴ = J * (J * Xᴴ * J) * J := by
          simp only [← Matrix.mul_assoc, hJ, Matrix.one_mul, mul_J_J hJ]
      _ = -(J * (-(J * Xᴴ * J)) * J) := by simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]
      _ = -(J * X * J) := by rw [h]

theorem reG_mem (M : Matrix n n ℂ) : reG J M ∈ lieJ J := by
  rw [mem_lieJ_iff_thetaG hJ, reG, thetaG_smul, thetaG_add, thetaG_thetaG hJ hJh,
    add_comm (thetaG J M)]
  congr 1
  simp

theorem imG_mem (M : Matrix n n ℂ) : imG J M ∈ lieJ J := by
  rw [mem_lieJ_iff_thetaG hJ, imG, thetaG_smul, thetaG_sub, thetaG_thetaG hJ hJh,
    ← neg_sub M (thetaG J M), smul_neg, ← neg_smul]
  congr 1
  simp <;> ring

omit hJ hJh in
theorem reG_add_I_smul_imG (M : Matrix n n ℂ) : M = reG J M + Complex.I • imG J M := by
  rw [reG, imG, smul_smul, show Complex.I * -(Complex.I / 2) = 1 / 2 by
    rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I, neg_div, neg_neg], ← smul_add,
    add_add_sub_cancel, ← two_smul ℂ M, smul_smul]
  norm_num

theorem eq_reG_imG_of_eq {M X Y : Matrix n n ℂ} (hX : X ∈ lieJ J) (hY : Y ∈ lieJ J)
    (hM : M = X + Complex.I • Y) : X = reG J M ∧ Y = imG J M := by
  have hM' : thetaG J M = X - Complex.I • Y := by
    rw [hM, thetaG_add, thetaG_smul, (mem_lieJ_iff_thetaG hJ).1 hX,
      (mem_lieJ_iff_thetaG hJ).1 hY, Complex.star_def, Complex.conj_I, neg_smul, ← sub_eq_add_neg]
  refine ⟨?_, ?_⟩
  · rw [reG, hM', hM, add_add_sub_cancel, ← two_smul ℂ X, smul_smul]
    norm_num
  · rw [imG, hM', hM, add_sub_sub_cancel, ← two_smul ℂ, smul_smul, smul_smul,
      show -(Complex.I / 2) * 2 * Complex.I = 1 by
        rw [neg_mul, neg_mul, div_mul_cancel₀ _ two_ne_zero, Complex.I_mul_I, neg_neg], one_smul]

theorem existsUnique_complexification (M : Matrix n n ℂ) :
    ∃! XY : Matrix n n ℂ × Matrix n n ℂ, XY.1 ∈ lieJ J ∧ XY.2 ∈ lieJ J ∧ M = XY.1 + Complex.I • XY.2 :=
  ⟨(reG J M, imG J M), ⟨reG_mem hJ hJh M, imG_mem hJ hJh M, reG_add_I_smul_imG M⟩,
    fun XY h => by
      obtain ⟨h1, h2⟩ := eq_reG_imG_of_eq hJ hJh h.1 h.2.1 h.2.2
      exact Prod.ext h1 h2⟩

end Complexification

end CompanionTheory.D.Upq
