import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBilinCyclic

noncomputable section

namespace GlobalTheory.HCComm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def flip {n : ℕ} (M : Mt g n) : Mt g n := (M.submatrix Fin.revPerm Fin.revPerm).transpose

theorem flip_apply {n : ℕ} (M : Mt g n) (i j : Fin n) : flip M i j = M j.rev i.rev := rfl

theorem flip_mul {n : ℕ} (M N : Mt g n) : flip (M * N) = flip N * flip M := by
  unfold flip
  rw [← Matrix.submatrix_mul_equiv M N Fin.revPerm Fin.revPerm Fin.revPerm, Matrix.transpose_mul]

theorem flip_one {n : ℕ} : flip (1 : Mt g n) = 1 := by
  unfold flip
  rw [Matrix.submatrix_one_equiv, Matrix.transpose_one]

theorem flip_flip {n : ℕ} (M : Mt g n) : flip (flip M) = M := by
  ext i j
  simp only [flip_apply, Fin.rev_rev]

private lemma one_submatrix_rev_mul_apply {n : ℕ} (A : Mt g n) (i j : Fin n) :
    ((1 : Mt g n).submatrix Fin.rev id * A) i j = A i.rev j := by
  simp [Matrix.mul_apply, Matrix.one_apply]

private lemma mul_one_submatrix_rev_apply {n : ℕ} (A : Mt g n) (i j : Fin n) :
    (A * (1 : Mt g n).submatrix Fin.rev id) i j = A i j.rev := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp Fin.revPerm]
  simp [Matrix.one_apply]

theorem flip_similar {n : ℕ} (M : Mt g n) : ∃ P : Mt g n, IsUnit P ∧ P * M = flip M * P := by

  obtain ⟨Q, hQ, hQM⟩ := GlobalTheory.SimilarTranspose.main (ZMod g) (Fin n) M
  have hJJ : (1 : Mt g n).submatrix Fin.rev id * (1 : Mt g n).submatrix Fin.rev id = 1 := by
    ext i j
    rw [one_submatrix_rev_mul_apply]
    simp [Matrix.one_apply]
  have hflip : flip M = (1 : Mt g n).submatrix Fin.rev id * M.transpose *
      (1 : Mt g n).submatrix Fin.rev id := by
    ext i j
    rw [mul_one_submatrix_rev_apply, one_submatrix_rev_mul_apply, flip_apply, Matrix.transpose_apply]
  generalize (1 : Mt g n).submatrix Fin.rev id = J at hJJ hflip
  refine ⟨J * Q, IsUnit.mul ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩ hQ, ?_⟩
  have hJJQ : J * (J * Q) = Q := by rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  rw [hflip]
  simp only [Matrix.mul_assoc, hJJQ, hQM]

def flipG {n : ℕ} (x : Gn g n) : Gn g n where
  val := flip (x : Mt g n)
  inv := flip ((x⁻¹ : Gn g n) : Mt g n)
  val_inv := by rw [← flip_mul, Units.inv_mul, flip_one]
  inv_val := by rw [← flip_mul, Units.mul_inv, flip_one]

theorem flipG_coe {n : ℕ} (x : Gn g n) : ((flipG x : Gn g n) : Mt g n) = flip (x : Mt g n) := rfl

theorem flipG_mul {n : ℕ} (x y : Gn g n) : flipG (x * y) = flipG y * flipG x := by
  apply Units.ext
  simp only [flipG_coe, Units.val_mul, flip_mul]

theorem flipG_inv {n : ℕ} (x : Gn g n) : flipG x⁻¹ = (flipG x)⁻¹ := by
  apply Units.ext
  rfl

theorem flipG_flipG {n : ℕ} (x : Gn g n) : flipG (flipG x) = x := by
  apply Units.ext
  simp only [flipG_coe, flip_flip]

def flipE (n : ℕ) : Gn g n ≃ Gn g n := ⟨flipG, flipG, flipG_flipG, flipG_flipG⟩

theorem flipG_conj {n : ℕ} (x : Gn g n) : ∃ p : Gn g n, flipG x = p * x * p⁻¹ := by
  obtain ⟨P, hP, hPx⟩ := flip_similar (x : Mt g n)
  refine ⟨hP.unit, Units.ext ?_⟩
  have h1 : ((hP.unit : Gn g n) : Mt g n) = P := hP.unit_spec
  have h2 : ((hP.unit : Gn g n) : Mt g n) * ((hP.unit⁻¹ : Gn g n) : Mt g n) = 1 := hP.unit.mul_inv
  rw [h1] at h2
  rw [flipG_coe, Units.val_mul, Units.val_mul, h1, hPx, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  unfold toG
  rw [dif_pos (Units.isUnit x)]
  exact Units.ext rfl

theorem class_flip {n : ℕ} {α : Gn g n → ℂ} (hα : IsClass α) (M : Mt g n) :
    α (toG (flip M)) = α (toG M) := by
  by_cases hM : IsUnit M
  · have e1 : toG M = hM.unit := by
      unfold toG
      rw [dif_pos hM]
    have e2 : toG (flip M) = flipG hM.unit := by
      rw [← toG_coe (flipG hM.unit), flipG_coe, IsUnit.unit_spec]
    obtain ⟨p, hp⟩ := flipG_conj hM.unit
    rw [e1, e2, hp]
    exact hα _ _
  · have hF : ¬ IsUnit (flip M) := by
      intro h
      apply hM
      have e : flip (flip M) = ((flipG h.unit : Gn g n) : Mt g n) := by
        rw [flipG_coe, IsUnit.unit_spec]
      rw [flip_flip] at e
      rw [e]
      exact Units.isUnit _
    unfold toG
    rw [dif_neg hM, dif_neg hF]

theorem inPar_flip {a b : ℕ} (M : Mt g (a + b)) : InPar b (flip M) ↔ InPar a M := by
  constructor
  · intro h i j hj hi
    have hi' := i.isLt
    have hj' := j.isLt
    have := h j.rev i.rev (by simp only [Fin.val_rev]; omega) (by simp only [Fin.val_rev]; omega)
    rwa [flip_apply, Fin.rev_rev, Fin.rev_rev] at this
  · intro h i j hj hi
    have hi' := i.isLt
    have hj' := j.isLt
    rw [flip_apply]
    exact h j.rev i.rev (by simp only [Fin.val_rev]; omega) (by simp only [Fin.val_rev]; omega)

private lemma entN_of_lt {n : ℕ} (M : Mt g n) (x y : ℕ) (hx : x < n) (hy : y < n) :
    entN M x y = M ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold entN
  rw [dif_pos ⟨hx, hy⟩]

theorem tl_flip {a b : ℕ} (M : Mt g (a + b)) : tl b (flip M) = flip (br a b M) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [flip_apply]
  simp only [tl, br]
  rw [entN_of_lt (flip M) i j (by omega) (by omega),
    entN_of_lt M (a + j.rev) (a + i.rev) (by simp only [Fin.val_rev]; omega)
      (by simp only [Fin.val_rev]; omega), flip_apply]
  congr 1 <;> ext <;> simp only [Fin.val_rev] <;> omega

private lemma entN_eq_apply_of_lt_of_lt {n : ℕ} (M : Mt g n) (x y : ℕ) (hx : x < n) (hy : y < n) :
    entN M x y = M ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold entN
  rw [dif_pos ⟨hx, hy⟩]

theorem br_flip {a b : ℕ} (M : Mt g (a + b)) : br b a (flip M) = flip (tl a M) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [flip_apply]
  simp only [tl, br]
  rw [entN_eq_apply_of_lt_of_lt (flip M) (b + i) (b + j) (by omega) (by omega),
    entN_eq_apply_of_lt_of_lt M j.rev i.rev (by simp only [Fin.val_rev]; omega)
      (by simp only [Fin.val_rev]; omega), flip_apply]
  congr 1 <;> ext <;> simp only [Fin.val_rev] <;> omega

private lemma sum_flipG_conj_eq_sum_conj_flipG {n : ℕ} (F : Gn g n → ℂ) (w : Gn g n) :
    ∑ y : Gn g n, F (flipG (y⁻¹ * w * y)) = ∑ y : Gn g n, F (y⁻¹ * flipG w * y) := by
  refine Fintype.sum_bijective (fun y => (flipG y)⁻¹) ?_ _ _ ?_
  · refine Function.bijective_iff_has_inverse.mpr ⟨fun v => flipG v⁻¹, ?_, ?_⟩
    · intro y
      simp only [inv_inv, flipG_flipG]
    · intro v
      simp only [flipG_flipG, inv_inv]
  · intro y
    simp only [flipG_mul, flipG_inv, inv_inv, mul_assoc]

private lemma sum_conj_conj_eq_sum_conj {n : ℕ} (F : Gn g n → ℂ) (w p : Gn g n) :
    ∑ y : Gn g n, F (y⁻¹ * (p * w * p⁻¹) * y) = ∑ y : Gn g n, F (y⁻¹ * w * y) := by
  refine Fintype.sum_bijective (fun y => p⁻¹ * y) (Group.mulLeft_bijective p⁻¹) _ _ ?_
  intro y
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem main : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ),
    IsClass α → IsClass β → n = a + b → hc a b α β n = hc b a β α n := by
  intro g _ a b n α β hα hβ hn
  subst hn
  funext x

  have key : ∀ z : Gn g (a + b),
      (if InPar b ((flipG z : Gn g (a + b)) : Mt g (a + b)) then
        β (toG (tl b ((flipG z : Gn g (a + b)) : Mt g (a + b)))) *
          α (toG (br b a ((flipG z : Gn g (a + b)) : Mt g (a + b)))) else 0) =
      (if InPar a (z : Mt g (a + b)) then
        α (toG (tl a (z : Mt g (a + b)))) * β (toG (br a b (z : Mt g (a + b)))) else 0) := by
    intro z
    simp only [flipG_coe, inPar_flip, tl_flip, br_flip, class_flip hβ, class_flip hα]
    rw [mul_comm]
  have hcard : (Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card =
      (Finset.univ.filter fun p : Gn g (a + b) => InPar b (p : Mt g (a + b))).card := by
    refine Finset.card_nbij' flipG flipG ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq ⊢
      rw [flipG_coe, inPar_flip]
      exact hq
    · intro q hq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq ⊢
      rw [flipG_coe]
      apply (inPar_flip (a := a) (b := b) (flip (q : Mt g (a + b)))).mp
      rwa [flip_flip]
    · intro q _
      exact flipG_flipG q
    · intro q _
      exact flipG_flipG q
  obtain ⟨p, hp⟩ := flipG_conj x
  let Fba : Gn g (a + b) → ℂ := fun z =>
    if InPar b (z : Mt g (a + b)) then
      β (toG (tl b (z : Mt g (a + b)))) * α (toG (br b a (z : Mt g (a + b)))) else 0
  have e1 : (∑ y : Gn g (a + b), if InPar a ((y⁻¹ * x * y : Gn g (a + b)) : Mt g (a + b)) then
      α (toG (tl a ((y⁻¹ * x * y : Gn g (a + b)) : Mt g (a + b)))) *
        β (toG (br a b ((y⁻¹ * x * y : Gn g (a + b)) : Mt g (a + b)))) else 0) =
      ∑ y : Gn g (a + b), Fba (y⁻¹ * x * y) := by
    calc _ = ∑ y : Gn g (a + b), Fba (flipG (y⁻¹ * x * y)) :=
          Finset.sum_congr rfl fun y _ => (key _).symm
      _ = ∑ y : Gn g (a + b), Fba (y⁻¹ * flipG x * y) := sum_flipG_conj_eq_sum_conj_flipG Fba x
      _ = ∑ y : Gn g (a + b), Fba (y⁻¹ * x * y) := by
          rw [hp]
          exact sum_conj_conj_eq_sum_conj Fba x p
  simp only [hc, hcT]
  rw [hcard]
  congr 1

end GlobalTheory.HCComm
