import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section Basic

variable {A : Type} [CommRing A] {r : ℕ}

theorem qa_subY_X_some (v : Fin (r + 1 + 1) × Fin (r + 1 + 1)) (j : Fin r) (h : midOf v.2 = some j) :
    subY A r (X v) = ∑ i : Fin r, C (X (i, j)) * X (v.1, midI r i) := by
  unfold subY
  rw [aeval_X]
  simp only [h]

theorem qa_subY_X_none (v : Fin (r + 1 + 1) × Fin (r + 1 + 1)) (h : midOf v.2 = none) :
    subY A r (X v) = X v := by
  unfold subY
  rw [aeval_X]
  simp only [h]

theorem qa_subY_C (a : A) : subY A r (C a) = C (C a) := by
  unfold subY
  exact aeval_C _ a

end Basic

theorem qa_rowAct_X {R : Type} [CommRing R] {k n : ℕ} (g : Matrix (Fin k) (Fin k) R) (x : Fin k × Fin n) :
    rowAct R g (X x) = ∑ b : Fin k, C (g x.1 b) * X (b, x.2) := by
  unfold rowAct
  exact aeval_X _ x

theorem qa_rowAct_C {R : Type} [CommRing R] {k n : ℕ} (g : Matrix (Fin k) (Fin k) R) (c : R) :
    rowAct R (n := n) g (C c) = C c := by
  unfold rowAct
  exact aeval_C _ c

theorem subMapP : SubMapP := by
  intro A B _ _ φ r v
  have h : ((subY B r).toRingHom.comp (map φ)) = ((map (map φ)).comp (subY A r).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show subY B r (map φ (C a)) = map (map φ) (subY A r (C a))
      rw [map_C, qa_subY_C, qa_subY_C, map_C, map_C]
    · intro w
      show subY B r (map φ (X w)) = map (map φ) (subY A r (X w))
      rw [map_X]
      cases hm : midOf w.2 with
      | none => rw [qa_subY_X_none w hm, qa_subY_X_none w hm, map_X]
      | some j =>
        rw [qa_subY_X_some w j hm, qa_subY_X_some w j hm, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_C, map_X, map_X]
  exact RingHom.congr_fun h v

def rowInd {k n : ℕ} (a : Fin k) : Fin k × Fin n → ℕ := fun v => if v.1 = a then 1 else 0

theorem qa_weight_rowInd {k n : ℕ} (a : Fin k) (u : Fin k × Fin n →₀ ℕ) :
    Finsupp.weight (rowInd a) u = rowDeg u a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, rowDeg]
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [rowInd]
  · intro b _ hb
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [rowInd, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem qa_iwh_pow {σ R M : Type} [CommSemiring R] [AddCommMonoid M] {w : σ → M} {φ : MvPolynomial σ R} {n : M}
    (h : IsWeightedHomogeneous w φ n) (k : ℕ) : IsWeightedHomogeneous w (φ ^ k) (k • n) := by
  induction k with
  | zero =>
    rw [pow_zero, zero_smul]
    exact isWeightedHomogeneous_one R w
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul h

theorem subRowP : SubRowP := by
  classical
  intro A _ r a d v hv
  have hX : ∀ x, IsWeightedHomogeneous (rowInd a) (subY A r (X x)) (rowInd a x) := by
    intro x
    cases hm : midOf x.2 with
    | none =>
      rw [qa_subY_X_none x hm]
      exact isWeightedHomogeneous_X _ _ _
    | some j =>
      rw [qa_subY_X_some x j hm]
      refine IsWeightedHomogeneous.sum _ _ _ fun i _ => ?_
      have h := (isWeightedHomogeneous_C (rowInd a) (X (i, j) : MvPolynomial (Fin r × Fin r) A)).mul
        (isWeightedHomogeneous_X (MvPolynomial (Fin r × Fin r) A) (rowInd a) (x.1, midI r i))
      rw [zero_add] at h
      exact h
  have hmain : IsWeightedHomogeneous (rowInd a) (subY A r v) d := by
    rw [← support_sum_monomial_coeff v, map_sum]
    refine IsWeightedHomogeneous.sum _ _ _ fun u hu => ?_
    have hd : rowDeg u a = d := hv u (mem_support_iff.1 hu)
    have e : (monomial u (coeff u v) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) =
        C (coeff u v) * ∏ x ∈ u.support, X x ^ u x := monomial_eq
    rw [e, map_mul (subY A r), qa_subY_C, map_prod]
    have h1 : IsWeightedHomogeneous (rowInd a) (∏ x ∈ u.support, subY A r (X x ^ u x))
        (∑ x ∈ u.support, u x • rowInd a x) :=
      IsWeightedHomogeneous.prod _ _ _ fun x _ => by
        rw [map_pow]
        exact qa_iwh_pow (hX x) (u x)
    have h2 : ∑ x ∈ u.support, u x • rowInd a x = d := by
      have h0 := qa_weight_rowInd a u
      rw [Finsupp.weight_apply] at h0
      exact h0.trans hd
    have h3 := (isWeightedHomogeneous_C (rowInd a) (C (coeff u v) : MvPolynomial (Fin r × Fin r) A)).mul h1
    rw [zero_add, h2] at h3
    exact h3
  intro u hu
  rw [← qa_weight_rowInd a u]
  exact hmain hu

theorem qa_subY_rowAct {A : Type} [CommRing A] {r : ℕ} (g : Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) A)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) :
    subY A r (rowAct A g v) = rowAct (MvPolynomial (Fin r × Fin r) A) (g.map C) (subY A r v) := by
  have h : (subY A r).toRingHom.comp (rowAct A g).toRingHom =
      (rowAct (MvPolynomial (Fin r × Fin r) A) (g.map C)).toRingHom.comp (subY A r).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show subY A r (rowAct A g (C a)) = rowAct _ (g.map C) (subY A r (C a))
      rw [qa_rowAct_C, qa_subY_C, qa_rowAct_C]
    · intro x
      show subY A r (rowAct A g (X x)) = rowAct _ (g.map C) (subY A r (X x))
      rw [qa_rowAct_X, map_sum]
      cases hm : midOf x.2 with
      | none =>
        rw [qa_subY_X_none x hm, qa_rowAct_X]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul (subY A r), qa_subY_C, qa_subY_X_none (b, x.2) hm]
        try rfl
      | some j =>
        rw [qa_subY_X_some x j hm, map_sum]
        have e1 : ∀ b, subY A r (C (g x.1 b) * X (b, x.2)) =
            ∑ i, C (C (g x.1 b)) * (C (X (i, j)) * X (b, midI r i)) := by
          intro b
          rw [map_mul (subY A r), qa_subY_C, qa_subY_X_some (b, x.2) j hm, Finset.mul_sum]
        have e2 : ∀ i, rowAct (MvPolynomial (Fin r × Fin r) A) (g.map C) (C (X (i, j)) * X (x.1, midI r i)) =
            ∑ b, C (X (i, j)) * (C (C (g x.1 b)) * X (b, midI r i)) := by
          intro i
          rw [map_mul (rowAct (MvPolynomial (Fin r × Fin r) A) (g.map C)), qa_rowAct_C, qa_rowAct_X, Finset.mul_sum]
          try rfl
        simp only [e1, e2]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
        ring
  exact RingHom.congr_fun h v

end Formalism.MainNotions.flipOneThree.Pf

end
