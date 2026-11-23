import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagPivotAlgIndep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

namespace FlagPivotAlgIndep

variable (F : Type) [Field F] (n : ℕ)

abbrev genFrac (p : Fin n × Fin n) : FractionRing (MvPolynomial (Fin n × Fin n) F) :=
  algebraMap (MvPolynomial (Fin n × Fin n) F) _ (X p)

theorem genFrac_ne_zero (p : Fin n × Fin n) : genFrac F n p ≠ 0 := by
  simp only [genFrac, ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact X_ne_zero p

def spec (p : Fin n × Fin n) : FractionRing (MvPolynomial (Fin n × Fin n) F) :=
  if (p.2 : ℕ) < p.1 then 0
  else if h : (p.1 : ℕ) = 0 then genFrac F n p
  else genFrac F n p / genFrac F n (⟨p.1 - 1, by omega⟩, ⟨p.1 - 1, by omega⟩)

theorem prod_spec (m : ℕ) (hm : m < n) (c : Fin n) (hc : m ≤ (c : ℕ)) :
    (∏ i : Fin m, spec F n (⟨i, by omega⟩, ⟨i, by omega⟩)) * spec F n (⟨m, hm⟩, c) = genFrac F n (⟨m, hm⟩, c) := by
  induction m generalizing c with
  | zero => simp [spec]
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega) ⟨m, by omega⟩ le_rfl]
    have e : (⟨m + 1 - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ := Fin.ext (by simp)
    simp only [spec, show ¬ ((c : ℕ) < m + 1) by omega, if_false, show m + 1 ≠ 0 by omega, dif_neg, not_false_eq_true, e]
    exact mul_div_cancel₀ _ (genFrac_ne_zero F n _)

theorem spec_pivotMinor (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    aeval (spec F n) (pivotMinor (genMat F n) a b) = genFrac F n (Fin.castLE (Nat.sub_le n 1) a, b) := by
  have ha : (a : ℕ) < n := by have := a.2; omega
  unfold pivotMinor
  rw [AlgHom.map_det, Matrix.det_of_isUpperTriangular]
  · rw [Fin.prod_univ_castSucc]
    refine Eq.trans ?_ (prod_spec F n a ha b hab)
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X]
      rfl
    · simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X]
      rfl
  · intro i j hji
    have hji' : (j : ℕ) < i := hji
    have hj : (j : ℕ) < a := by have := i.2; omega
    simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X, spec, hj, hji']

theorem proof : FlagPivotAlgIndep.Statement := by
  intro F _ n
  refine AlgebraicIndependent.of_comp (aeval (spec F n)) ?_
  have hfun : ⇑(aeval (spec F n)) ∘
        (fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => pivotMinor (genMat F n) q.1 q.2.1) =
      ⇑(IsScalarTower.toAlgHom F (MvPolynomial (Fin n × Fin n) F) (FractionRing (MvPolynomial (Fin n × Fin n) F))) ∘
        ((X : Fin n × Fin n → MvPolynomial (Fin n × Fin n) F) ∘
          fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => (Fin.castLE (Nat.sub_le n 1) q.1, q.2.1)) := by
    funext q
    exact spec_pivotMinor F n q.1 q.2.1 q.2.2
  rw [hfun]
  refine AlgebraicIndependent.map' ?_ (IsFractionRing.injective _ _)
  refine (algebraicIndependent_X (Fin n × Fin n) F).comp _ ?_
  rintro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : a = a' := Fin.ext (by simpa using congrArg Fin.val h1)
  subst h1' h2
  rfl

end FlagPivotAlgIndep

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
