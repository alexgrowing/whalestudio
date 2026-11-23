import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.UnitaryLieComplexification

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

noncomputable def cj (J Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := -(J⁻¹ * Zᴴ * J)

theorem cj_add (Z W : Matrix (Fin n) (Fin n) ℂ) : cj J (Z + W) = cj J Z + cj J W := by
  simp only [cj, conjTranspose_add, mul_add, add_mul, neg_add]

theorem cj_sub (Z W : Matrix (Fin n) (Fin n) ℂ) : cj J (Z - W) = cj J Z - cj J W := by
  simp only [cj, conjTranspose_sub, mul_sub, sub_mul]
  abel

theorem cj_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : cj J (c • Z) = star c • cj J Z := by
  simp only [cj, conjTranspose_smul, mul_smul_comm, smul_mul_assoc, smul_neg]

theorem cj_cj (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : cj J (cj J Z) = Z := by
  simp only [cj, conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ,
    mul_neg, neg_mul, neg_neg, Matrix.mul_assoc, Matrix.nonsing_inv_mul J hu, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hu, Matrix.one_mul]

theorem mem_iff_cj (hu : IsUnit J.det) (X : Matrix (Fin n) (Fin n) ℂ) : X ∈ lieU J ↔ cj J X = X := by
  change Xᴴ * J + J * X = 0 ↔ _
  constructor
  · intro h
    rw [cj, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h, mul_neg, neg_neg, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul J hu, Matrix.one_mul]
  · intro h
    have : J * X = -(Xᴴ * J) := by
      conv_lhs => rw [← h]
      rw [cj, mul_neg, Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hu, Matrix.one_mul]
    rw [this, add_neg_cancel]

noncomputable def rePart (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : lieU J :=
  ⟨(1 / 2 : ℂ) • (Z + cj J Z), by
    rw [mem_iff_cj hu, cj_smul, cj_add, cj_cj hJ hu, add_comm]
    simp⟩

noncomputable def imPart (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) : lieU J :=
  ⟨(1 / (2 * Complex.I) : ℂ) • (Z - cj J Z), by
    rw [mem_iff_cj hu, cj_smul, cj_sub, cj_cj hJ hu, ← neg_sub Z, smul_neg, ← neg_smul]
    congr 1
    simp⟩

theorem re_add_im (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (rePart hJ hu Z).1 + Complex.I • (imPart hJ hu Z).1 = Z := by
  have h : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  simp only [rePart, imPart, smul_smul, h]
  module

theorem cj_mk (hu : IsUnit J.det) (X Y : lieU J) :
    cj J (X.1 + Complex.I • Y.1) = X.1 - Complex.I • Y.1 := by
  rw [cj_add, cj_smul, (mem_iff_cj hu _).1 X.2, (mem_iff_cj hu _).1 Y.2]
  simp [sub_eq_add_neg]

theorem rePart_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (X Y : lieU J) :
    rePart hJ hu (X.1 + Complex.I • Y.1) = X := by
  apply Subtype.ext
  simp only [rePart, cj_mk hu]
  module

theorem imPart_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (X Y : lieU J) :
    imPart hJ hu (X.1 + Complex.I • Y.1) = Y := by
  apply Subtype.ext
  simp only [imPart, cj_mk hu]
  have h : (1 / (2 * Complex.I)) * (2 * Complex.I) = 1 := by field_simp
  have h2 : X.1 + Complex.I • Y.1 - (X.1 - Complex.I • Y.1) = (2 * Complex.I) • Y.1 := by module
  rw [h2, smul_smul, h, one_smul]

theorem exists_mk (hJ : Jᴴ = J) (hu : IsUnit J.det) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ X Y : lieU J, Z = X.1 + Complex.I • Y.1 := ⟨_, _, (re_add_im hJ hu Z).symm⟩

theorem exists_extension (hJ : Jᴴ = J) (hu : IsUnit J.det) {A : Type} [Ring A] [Algebra ℂ A] (ρ : lieU J → A)
    (hadd : ∀ X Y, ρ (X + Y) = ρ X + ρ Y) (hsm : ∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X)
    (hlie : ∀ X Y Z : lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A,
      (∀ Z, R Z = ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)) ∧ (∀ X : lieU J, R X.1 = ρ X) ∧
      ∀ Z W, R (Z * W - W * Z) = R Z * R W - R W * R Z := by
  have hsub : ∀ X Y, ρ (X - Y) = ρ X - ρ Y := by
    intro X Y
    have := hadd (X - Y) Y
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have h0 : ρ 0 = 0 := by
    have := hsub 0 0
    rwa [sub_self, sub_self] at this
  let r : Matrix (Fin n) (Fin n) ℂ → A := fun Z => ρ (rePart hJ hu Z) + Complex.I • ρ (imPart hJ hu Z)
  have key : ∀ X Y : lieU J, r (X.1 + Complex.I • Y.1) = ρ X + Complex.I • ρ Y := by
    intro X Y
    simp only [r, rePart_mk, imPart_mk]
  have hII : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (m : M), Complex.I • Complex.I • m = -m := by
    intro M _ _ m
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hbr : ∀ X Y : lieU J, ρ ⁅X, Y⁆ = ρ X * ρ Y - ρ Y * ρ X := fun X Y => hlie X Y _ rfl
  have hbc : ∀ X Y : lieU J, (⁅X, Y⁆ : lieU J).1 = X.1 * Y.1 - Y.1 * X.1 := fun X Y => rfl
  refine ⟨{ toFun := r, map_add' := ?_, map_smul' := ?_ }, fun Z => rfl, ?_, ?_⟩
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : X.1 + Complex.I • Y.1 + (X'.1 + Complex.I • Y'.1) = (X + X').1 + Complex.I • (Y + Y').1 := by
      change _ = (X.1 + X'.1) + Complex.I • (Y.1 + Y'.1)
      module
    rw [this, key, key, key, hadd, hadd]
    module
  · intro c Z
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    generalize c.re = a at hc
    generalize c.im = b at hc
    subst hc
    have : ((a : ℂ) + (b : ℂ) * Complex.I) • (X.1 + Complex.I • Y.1) =
        (a • X - b • Y).1 + Complex.I • (b • X + a • Y).1 := by
      change _ = ((a : ℂ) • X.1 - (b : ℂ) • Y.1) + Complex.I • ((b : ℂ) • X.1 + (a : ℂ) • Y.1)
      simp only [add_smul, smul_add, mul_smul, hII]
      module
    rw [this, key, key, hsub, hadd, hsm, hsm, hsm, hsm]
    simp only [RingHom.id_apply, add_smul, smul_add, mul_smul, hII]
    module
  · intro X
    have := key X 0
    simpa [h0] using this
  · intro Z W
    obtain ⟨X, Y, rfl⟩ := exists_mk hJ hu Z
    obtain ⟨X', Y', rfl⟩ := exists_mk hJ hu W
    have : (X.1 + Complex.I • Y.1) * (X'.1 + Complex.I • Y'.1) - (X'.1 + Complex.I • Y'.1) * (X.1 + Complex.I • Y.1) =
        (⁅X, X'⁆ - ⁅Y, Y'⁆ : lieU J).1 + Complex.I • (⁅X, Y'⁆ + ⁅Y, X'⁆ : lieU J).1 := by
      change _ = ((X.1 * X'.1 - X'.1 * X.1) - (Y.1 * Y'.1 - Y'.1 * Y.1)) +
        Complex.I • ((X.1 * Y'.1 - Y'.1 * X.1) + (Y.1 * X'.1 - X'.1 * Y.1))
      simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add, hII]
      module
    change r _ = r _ * r _ - r _ * r _
    rw [this, key, key, key, hsub, hadd, hbr, hbr, hbr, hbr]
    simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_add, hII]
    module

theorem glRel_and_span : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∃ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) ∧ ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ X Y, ρ (X + Y) = ρ X + ρ Y) → (∀ (c : ℝ) X, ρ (c • X) = (c : ℂ) • ρ X) → (∀ X Y Z : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ Z = ρ X * ρ Y - ρ Y * ρ X) → Formalism.REAL.GlRel (fun a b => ρ (P a b) + Complex.I • ρ (Q a b)) ∧ ∀ X, ρ X ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => ρ (P p.1 p.2) + Complex.I • ρ (Q p.1 p.2)) := by
  intro n J hJ hu
  refine ⟨fun a b => rePart hJ hu (Matrix.single a b 1), fun a b => imPart hJ hu (Matrix.single a b 1),
    fun a b => ⟨rfl, rfl⟩, ?_⟩
  intro A _ _ ρ hadd hsm hlie
  obtain ⟨R, hR, hX, hc⟩ := exists_extension hJ hu ρ hadd hsm hlie
  simp only [← hR]
  constructor
  · intro a b c d
    simp only
    rw [← hc, map_sub]
    congr 1
    · split_ifs with h
      · subst h; rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
    · split_ifs with h
      · subst h; rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne (h := h), map_zero]
  · intro X
    rw [← hX, Matrix.matrix_eq_sum_single X.1, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [map_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    have : Matrix.single a b (X.1 a b) = X.1 a b • Matrix.single a b (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)

end GlobalTheory.UnitaryLieComplexification
