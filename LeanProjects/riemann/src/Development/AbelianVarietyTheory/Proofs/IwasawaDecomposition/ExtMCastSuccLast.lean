import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.TilX

section Ext

variable {A : Type} [CommRing A] {N n : ℕ} (hN : N = n + 1)

def extM (_hN : N = n + 1) (g : Matrix (Fin n) (Fin n) A) : Matrix (Fin N) (Fin N) A := fun a b =>
  if ha : a.1 < n then (if hb : b.1 < n then g ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0) else if b.1 < n then 0 else 1

theorem extM_castSucc (g : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    extM (rfl : n + 1 = n + 1) g i.castSucc j.castSucc = g i j := by
  simp [extM]

theorem extM_castSucc_last (g : Matrix (Fin n) (Fin n) A) (i : Fin n) :
    extM (rfl : n + 1 = n + 1) g i.castSucc (Fin.last n) = 0 := by
  simp [extM]

theorem extM_last_castSucc (g : Matrix (Fin n) (Fin n) A) (j : Fin n) :
    extM (rfl : n + 1 = n + 1) g (Fin.last n) j.castSucc = 0 := by
  simp [extM]

theorem extM_last_last (g : Matrix (Fin n) (Fin n) A) :
    extM (rfl : n + 1 = n + 1) g (Fin.last n) (Fin.last n) = 1 := by
  simp [extM]

theorem extM_mulVec_iC (g : Matrix (Fin n) (Fin n) A) (x : Fin N → A) (i : Fin n) :
    (extM hN g *ᵥ x) (Br.iC hN i) = (g *ᵥ iniH hN x) i := by
  subst hN
  have e : Br.iC (rfl : n + 1 = n + 1) i = i.castSucc := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, e, extM_castSucc, extM_castSucc_last, zero_mul, add_zero]
  rfl

theorem extM_mulVec_iL (g : Matrix (Fin n) (Fin n) A) (x : Fin N → A) :
    (extM hN g *ᵥ x) (Br.iL hN) = x (Br.iL hN) := by
  subst hN
  have e : Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, e, extM_last_castSucc, extM_last_last, zero_mul,
    Finset.sum_const_zero, zero_add, one_mul]

theorem extM_one : extM hN (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  subst hN
  ext a b
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [extM_last_last]
  · rw [extM_last_castSucc, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
  · rw [extM_castSucc_last, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  · rw [extM_castSucc, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castSucc_inj]

theorem extM_mul (g h : Matrix (Fin n) (Fin n) A) : extM hN (g * h) = extM hN g * extM hN h := by
  subst hN
  ext a b
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [extM_last_last, extM_last_castSucc]
  · simp [extM_last_last, extM_last_castSucc]
  · simp [extM_castSucc_last]
  · simp [extM_castSucc, extM_castSucc_last, Matrix.mul_apply]

def extGL : GL (Fin n) A →* GL (Fin N) A :=
  Units.map { toFun := extM hN, map_one' := extM_one hN, map_mul' := extM_mul hN }

theorem extGL_val (g : GL (Fin n) A) : (extGL hN g : Matrix (Fin N) (Fin N) A) = extM hN g := rfl

theorem extGL_inv_val (g : GL (Fin n) A) :
    ((extGL hN g)⁻¹ : GL (Fin N) A).1 = extM hN ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  rw [← map_inv, extGL_val]

theorem eq_extM {M : Matrix (Fin N) (Fin N) A} {g : Matrix (Fin n) (Fin n) A}
    (h1 : ∀ (a : Fin N) (j : Fin n), M a (Br.iC hN j) = extM hN g a (Br.iC hN j))
    (h2 : ∀ a : Fin N, M a (Br.iL hN) = extM hN g a (Br.iL hN)) : M = extM hN g := by
  subst hN
  ext a b
  refine Fin.lastCases ?_ (fun j => ?_) b
  · exact h2 a
  · exact h1 a j

end Ext

end GlobalTheory.Mem.Col2.TilX

end
