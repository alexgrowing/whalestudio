import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl

open Matrix

namespace GlobalTheory.SatakeWeyl.InclusionMultiplication

variable {L : Type} [Field L] {n r : ℕ}

def incl (L : Type) [Field L] (e : Fin r → Fin n) : Matrix (Fin n) (Fin r) L :=
  Matrix.of fun a i => if a = e i then 1 else 0

theorem incl_mul_apply {p : Type} {e : Fin r → Fin n} (he : Function.Injective e) (M : Matrix (Fin r) p L)
    (i : Fin r) (j : p) : (incl L e * M) (e i) j = M i j := by
  simp [Matrix.mul_apply, incl, he.eq_iff]

theorem incl_mul_apply_of_not {p : Type} {e : Fin r → Fin n} (M : Matrix (Fin r) p L)
    {a : Fin n} (ha : a ∉ Set.range e) (j : p) : (incl L e * M) a j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : a ≠ e i := fun h => ha ⟨i, h.symm⟩
  simp [incl, this]

theorem mul_inclT_apply {p : Type} {e : Fin r → Fin n} (he : Function.Injective e) (M : Matrix p (Fin r) L)
    (i : p) (j : Fin r) : (M * (incl L e)ᵀ) i (e j) = M i j := by
  simp [Matrix.mul_apply, incl, he.eq_iff]

theorem mul_inclT_apply_of_not {p : Type} {e : Fin r → Fin n} (M : Matrix p (Fin r) L)
    (i : p) {a : Fin n} (ha : a ∉ Set.range e) : (M * (incl L e)ᵀ) i a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : a ≠ e j := fun h => ha ⟨j, h.symm⟩
  simp [incl, this]

theorem inclT_mul_incl {e : Fin r → Fin n} (he : Function.Injective e) : (incl L e)ᵀ * incl L e = 1 := by
  ext i j
  simp [Matrix.mul_apply, incl, he.eq_iff, Matrix.one_apply, eq_comm]

theorem antiJ_apply (i j : Fin n) : antiJ L n i j = if i.rev = j then 1 else 0 := by
  have : (i.val + j.val + 1 = n) ↔ i.rev = j := by
    have := i.2
    rw [Fin.ext_iff, Fin.val_rev]; omega
  simp only [antiJ, this]

theorem antiJ_transpose : (antiJ L n)ᵀ = antiJ L n := by
  ext i j
  simp only [Matrix.transpose_apply, antiJ, add_comm i.val j.val]

theorem antiJ_mul_incl {e : Fin r → Fin n} (hr : ∀ i, e i.rev = (e i).rev) :
    antiJ L n * incl L e = incl L e * antiJ L r := by
  ext a i
  have h1 : (antiJ L n * incl L e) a i = incl L e a.rev i := by
    simp [Matrix.mul_apply, antiJ_apply]
  have h2 : (incl L e * antiJ L r) a i = incl L e a i.rev := by
    simp [Matrix.mul_apply, antiJ_apply, Fin.rev_eq_iff]
  rw [h1, h2]
  simp [incl, hr, Fin.rev_eq_iff]

theorem inclT_mul_antiJ {e : Fin r → Fin n} (hr : ∀ i, e i.rev = (e i).rev) :
    (incl L e)ᵀ * antiJ L n = antiJ L r * (incl L e)ᵀ := by
  have := congrArg Matrix.transpose (antiJ_mul_incl (L := L) hr)
  rwa [Matrix.transpose_mul, Matrix.transpose_mul, antiJ_transpose, antiJ_transpose] at this

def ext1 (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) : Matrix (Fin n) (Fin n) L :=
  1 + incl L e * (M - 1) * (incl L e)ᵀ

theorem extendMatrixByIdentityAlongIndices_mul {e : Fin r → Fin n} (he : Function.Injective e) (M N : Matrix (Fin r) (Fin r) L) :
    ext1 e (M * N) = ext1 e M * ext1 e N := by
  have h : incl L e * (M - 1) * (incl L e)ᵀ * (incl L e * (N - 1) * (incl L e)ᵀ)
      = incl L e * ((M - 1) * (N - 1)) * (incl L e)ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl L e)ᵀ, inclT_mul_incl he, Matrix.one_mul]
  have h2 : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  unfold ext1
  rw [add_mul, mul_add, mul_add, h, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  abel

theorem conjTranspose_extendMatrixByIdentityAlongIndices (σ : L →+* L) (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) :
    cT σ (ext1 e M) = ext1 e (cT σ M) := by
  ext a b
  simp only [cT, ext1, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add,
    map_sum, map_mul, incl, Matrix.of_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite σ, map_one,
    map_zero, Finset.sum_mul]
  congr 1
  · simp only [eq_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [eq_comm (a := i) (b := j)]
    ring

theorem extendMatrixByIdentityAlongIndices_unitary [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {e : Fin r → Fin n} (he : Function.Injective e)
    (hr : ∀ i, e i.rev = (e i).rev) (M : Matrix (Fin r) (Fin r) L)
    (hM : cT σ M * antiJ L r * M = antiJ L r) :
    cT σ (ext1 e M) * antiJ L n * ext1 e M = antiJ L n := by
  have hJ : ∀ N : Matrix (Fin r) (Fin r) L, antiJ L n * ext1 e N
      = ext1 e (antiJ L r * N * antiJ L r) * antiJ L n := by
    intro N
    have h2 : antiJ L r * N * antiJ L r - 1 = antiJ L r * (N - 1) * antiJ L r := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, GlobalTheory.UnitarySwap.antiJ_mul_self]
    unfold ext1
    rw [h2, Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, antiJ_mul_incl hr]
    simp only [Matrix.mul_assoc]
    rw [inclT_mul_antiJ hr, ← Matrix.mul_assoc (antiJ L r) (antiJ L r), GlobalTheory.UnitarySwap.antiJ_mul_self,
      Matrix.one_mul]
  rw [conjTranspose_extendMatrixByIdentityAlongIndices, Matrix.mul_assoc, hJ, ← Matrix.mul_assoc, ← extendMatrixByIdentityAlongIndices_mul he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hM,
    GlobalTheory.UnitarySwap.antiJ_mul_self]
  simp [ext1]

end GlobalTheory.SatakeWeyl.InclusionMultiplication

open GlobalTheory.SatakeWeyl.InclusionMultiplication in

theorem GlobalTheory.SatakeWeyl.embExists : GlobalTheory.SatakeWeyl.EmbExists := by
  intro L _ _ σ n r e he hr
  choose f hf using fun g : GU σ r => exists_mat (σ := σ) (ext1 e (mat g)) (extendMatrixByIdentityAlongIndices_unitary σ he hr _ g.2)
  refine ⟨MonoidHom.mk' f fun a b => mat_injective ?_, fun g => ⟨fun i j => ?_, fun a b hab => ?_⟩⟩
  · rw [mat_mul, hf, hf, hf, mat_mul, extendMatrixByIdentityAlongIndices_mul he]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply, mul_inclT_apply he, incl_mul_apply he]
    simp [Matrix.one_apply, he.eq_iff]
  · rw [MonoidHom.mk'_apply, hf, ext1, Matrix.add_apply]
    rcases hab with h | h
    · rw [Matrix.mul_assoc, incl_mul_apply_of_not _ h, add_zero]
    · rw [mul_inclT_apply_of_not _ _ h, add_zero]
