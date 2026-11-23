import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetDFin

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

def phiF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Fin.cons 0 X

def piF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : Matrix (Fin N) (Fin N) ℂ := fun k l => X k l.succ

def colQ (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (c : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  fun k l => if l = c then X k 0 else 0

@[simp] theorem phiF_zero_row (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (j : Fin (N + 1)) : phiF X 0 j = 0 := rfl

@[simp] theorem phiF_succ_row (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (k : Fin N) (j : Fin (N + 1)) :
    phiF X k.succ j = X k j := rfl

def phiL (N : ℕ) : Matrix (Fin N) (Fin (N + 1)) ℂ →L[ℂ] Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := phiF
      map_add' := fun X Y => by
        ext i j; refine Fin.cases ?_ (fun k => ?_) i <;> simp
      map_smul' := fun a X => by
        ext i j; refine Fin.cases ?_ (fun k => ?_) i <;> simp }

def piL (N : ℕ) : Matrix (Fin N) (Fin (N + 1)) ℂ →L[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := piF
      map_add' := fun X Y => by ext k l; simp [piF]
      map_smul' := fun a X => by ext k l; simp [piF] }

@[simp] theorem phiL_apply (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : phiL N X = phiF X := rfl
@[simp] theorem piL_apply (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : piL N X = piF X := rfl

theorem phiF_single (k : Fin N) (j : Fin (N + 1)) :
    phiF (Matrix.single k j (1 : ℂ)) = Matrix.single k.succ j 1 := by
  ext i l
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [Matrix.single_apply, (Fin.succ_ne_zero k).symm]
  · simp [Matrix.single_apply, Fin.succ_inj]

theorem piF_single_succ (k : Fin N) (j : Fin N) :
    piF (Matrix.single k j.succ (1 : ℂ)) = Matrix.single k j 1 := by
  ext a b; simp [piF, Matrix.single_apply, Fin.succ_inj]

theorem piF_single_zero (k : Fin N) : piF (Matrix.single k (0 : Fin (N + 1)) (1 : ℂ)) = 0 := by
  ext a b; simp only [piF, Matrix.single_apply, Matrix.zero_apply]
  rw [if_neg]; rintro ⟨_, h⟩; exact Fin.succ_ne_zero b h.symm

theorem det_first_row_expansion (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (a : ℂ) (h : ∀ j, A 0 j = if j = 0 then a else 0) :
    A.det = a * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · simp [h]
  · intro j _ hj; simp [h, hj]
  · simp

theorem det_corner_perturbation (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    (1 + phiF X + s • Matrix.single 0 0 1).det = (1 + s) * (1 + piF X).det := by
  have hsub : (1 + phiF X + s • Matrix.single 0 0 1).submatrix Fin.succ Fin.succ = 1 + piF X := by
    ext k l
    simp [piF, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj, Fin.succ_ne_zero]
    intro h; exact absurd h.symm (Fin.succ_ne_zero k)
  rw [det_first_row_expansion _ (1 + s), hsub]
  intro j
  refine Fin.cases ?_ (fun m => ?_) j
  · simp [Matrix.one_apply, Matrix.single_apply]
  · simp [Matrix.one_apply, Matrix.single_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero m).symm]

theorem det_column_perturbation (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) (c : Fin N) :
    (1 + phiF X + s • Matrix.single 0 c.succ 1).det = (1 + piF X - s • colQ X c).det := by
  set A := 1 + phiF X + s • Matrix.single 0 c.succ (1 : ℂ) with hA
  have hne : c.succ ≠ (0 : Fin (N + 1)) := Fin.succ_ne_zero c
  have hz : ∀ k : Fin N, ((0 : Fin (N + 1)) = k.succ) ↔ False :=
    fun k => ⟨fun h => Fin.succ_ne_zero k h.symm, False.elim⟩
  rw [← Matrix.det_updateCol_add_smul_self A hne (-s)]
  rw [det_first_row_expansion _ 1]
  · rw [one_mul]
    congr 1
    ext k l
    by_cases hl : l = c
    · subst hl
      simp [A, Matrix.updateCol_apply, piF, colQ, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj,
        Fin.succ_ne_zero, hz]
      ring
    · have hl' : l.succ ≠ c.succ := fun h => hl (Fin.succ_inj.mp h)
      simp [A, Matrix.updateCol_apply, piF, colQ, Matrix.one_apply, Matrix.single_apply, Fin.succ_inj,
        hl, hl', Fin.succ_ne_zero, hz]
  · intro j
    by_cases hj : j = c.succ
    · subst hj
      simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, Fin.succ_ne_zero, hz]
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨m, rfl⟩
      · simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, hne.symm, hz]
      · have hm : m ≠ c := fun h => hj (by rw [h])
        simp [A, Matrix.updateCol_apply, Matrix.one_apply, Matrix.single_apply, hm, Fin.succ_ne_zero, hz,
          Fin.succ_inj, Ne.symm hm]

end PositivityTheory.Rg.Sw.LVs.CK
