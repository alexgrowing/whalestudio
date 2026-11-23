import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
import Formalism.SharpRestriction.GrowthBounds.ObjSeg

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

def genM (R : Type) [CommRing R] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
  Matrix.of fun a s => X (a, s)

def Nv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  if vec then X (c, 0) else (genM R m).adjugate (Fin.last m) c

def theta (R : Type) [CommRing R] (m : ℕ) (vec : Bool) :
    MvPolynomial (Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R :=
  aeval (Nv R m vec)

def act {R : Type} [CommRing R] {m : ℕ} (vec : Bool) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  if vec then g else g.adjugate.transpose

theorem genM_map_rowAct (R : Type) [CommRing R] (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    (genM R m).map (rowAct R g) = (g.map C) * genM R m := by
  ext a s
  simp only [Matrix.map_apply, genM, Matrix.of_apply, Matrix.mul_apply, rowAct, MvPolynomial.aeval_X]

theorem rowAct_Nv (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (c : Fin (m + 1)) :
    rowAct R g (Nv R m vec c) = ∑ b, C (act vec g c b) * Nv R m vec b := by
  cases vec with
  | true =>
    simp only [Nv, act, ↓reduceIte, rowAct, MvPolynomial.aeval_X]
  | false =>
    simp only [Nv, act, Bool.false_eq_true, ↓reduceIte]
    have h1 : (rowAct R g) ((genM R m).adjugate (Fin.last m) c) =
        ((genM R m).map (rowAct R g)).adjugate (Fin.last m) c :=
      congrFun (congrFun (RingHom.map_adjugate (rowAct R g).toRingHom (genM R m)) (Fin.last m)) c
    have h2 := RingHom.map_adjugate (MvPolynomial.C : R →+* MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) g
    simp only [RingHom.mapMatrix_apply] at h2
    rw [h1, genM_map_rowAct, Matrix.adjugate_mul_distrib, Matrix.mul_apply, ← h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.map_apply, Matrix.transpose_apply, mul_comm]

def lin {R : Type} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R) :
    MvPolynomial (Fin k) R →ₐ[R] MvPolynomial (Fin k) R :=
  aeval fun c => ∑ b, C (M c b) * X b

theorem rowAct_theta (R : Type) [CommRing R] (m : ℕ) (vec : Bool) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (P : MvPolynomial (Fin (m + 1)) R) :
    rowAct R g (theta R m vec P) = theta R m vec (lin (act vec g) P) := by
  have h : (rowAct R g).comp (theta R m vec) = (theta R m vec).comp (lin (act vec g)) := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply, theta, lin, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
    exact rowAct_Nv R m vec g c
  exact AlgHom.congr_fun h P

def psiM (R : Type) [CommRing R] (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1)) R) :=
  Matrix.of fun a s => (if a = s then X (Fin.last m) else 0) - (if a = Fin.last m ∧ s ≠ Fin.last m then X s else 0)

theorem psiM_apply (R : Type) [CommRing R] (m : ℕ) (a s : Fin (m + 1)) : psiM R m a s =
    (if a = s then X (Fin.last m) else 0) - (if a = Fin.last m ∧ s ≠ Fin.last m then X s else 0) := rfl

def psi (R : Type) [CommRing R] (m : ℕ) (vec : Bool) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) R →ₐ[R] MvPolynomial (Fin (m + 1)) R :=
  aeval fun v => if vec then (if v.2 = 0 then X v.1 else 0) else psiM R m v.1 v.2

def qf (R : Type) [CommRing R] (m : ℕ) (vec : Bool) : MvPolynomial (Fin (m + 1)) R :=
  if vec then 1 else X (Fin.last m) ^ (m - 1)

theorem psiM_det (R : Type) [CommRing R] (m : ℕ) : (psiM R m).det = X (Fin.last m) ^ (m + 1) := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [psiM_apply, Finset.prod_const]
  · intro i j h
    have hij : i < j := OrderDual.toDual_lt_toDual.mp h
    have h1 : i ≠ j := ne_of_lt hij
    have h2 : i ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
    simp [psiM_apply, h1, h2]

theorem psi_Nv (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (hm : 1 ≤ m) (vec : Bool) (c : Fin (m + 1)) :
    psi R m vec (Nv R m vec c) = qf R m vec * X c := by
  cases vec with
  | true => simp [psi, Nv, qf]
  | false =>
    simp only [Nv, qf, Bool.false_eq_true, ↓reduceIte]
    have hmap : (genM R m).map (psi R m false) = psiM R m := by
      ext a s
      simp [genM, psi]
    have h1 : (psi R m false) ((genM R m).adjugate (Fin.last m) c) =
        ((genM R m).map (psi R m false)).adjugate (Fin.last m) c :=
      congrFun (congrFun (RingHom.map_adjugate (psi R m false).toRingHom (genM R m)) (Fin.last m)) c
    rw [h1, hmap]
    have ht : (X (Fin.last m) : MvPolynomial (Fin (m + 1)) R) ≠ 0 := MvPolynomial.X_ne_zero _
    have hrow : ∀ s, ∑ a, (psiM R m).adjugate (Fin.last m) a * psiM R m a s =
        if Fin.last m = s then X (Fin.last m) ^ (m + 1) else 0 := by
      intro s
      have k := congrFun (congrFun (Matrix.adjugate_mul (psiM R m)) (Fin.last m)) s
      rw [Matrix.mul_apply, psiM_det] at k
      rw [k, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    have hsum : ∀ s, ∑ a, (psiM R m).adjugate (Fin.last m) a * psiM R m a s =
        (psiM R m).adjugate (Fin.last m) s * X (Fin.last m) -
          (if s ≠ Fin.last m then (psiM R m).adjugate (Fin.last m) (Fin.last m) * X s else 0) := by
      intro s
      simp only [psiM_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      congr 1
      by_cases hs : s = Fin.last m
      · simp [hs]
      · simp [hs]
    have hlast : (psiM R m).adjugate (Fin.last m) (Fin.last m) = X (Fin.last m) ^ m := by
      have e := (hsum (Fin.last m)).symm.trans (hrow (Fin.last m))
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, sub_zero] at e
      apply mul_right_cancel₀ ht
      rw [e, pow_succ]
    by_cases hc : c = Fin.last m
    · subst hc
      rw [hlast, ← pow_succ]
      congr 1
      omega
    · have e := (hsum c).symm.trans (hrow c)
      have hc' : Fin.last m ≠ c := Ne.symm hc
      simp only [hc, hc', ne_eq, not_false_eq_true, ↓reduceIte] at e
      rw [hlast, sub_eq_zero] at e
      apply mul_right_cancel₀ ht
      rw [e]
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring

end Formalism.L2.G.Model
