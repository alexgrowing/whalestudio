import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CollapseExponent

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

def varE (p : ℕ) (x : D.ML × Fin D.r) : D.EA :=
  Sum.elim (fun b => Finsupp.single (Sum.inl b, x.2) 1)
    (Sum.elim (fun t => Finsupp.single (Sum.inr t, x.2) 1)
      (Sum.elim (fun t => Finsupp.single (Sum.inr t, x.2) (D.P p t))
        (fun t => Finsupp.single (Sum.inr t, x.2) 1))) x.1

theorem ph_X (p : ℕ) (x : D.ML × Fin D.r) :
    D.ph p (X x : MvPolynomial (D.ML × Fin D.r) K) = monomial (D.varE p x) 1 := by
  obtain ⟨i, a⟩ := x
  unfold ph
  rw [aeval_X]
  rcases i with b | t | t | t <;> simp [varE, X, monomial_pow]

theorem phE_apply_inl (p : ℕ) (ζ : D.EM) (b : D.Lb) (a : Fin D.r) :
    D.phE p ζ (Sum.inl b, a) = ζ (D.mb b, a) := by
  simp [phE, collapseExponent, tpE]

theorem phE_apply_inr (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.phE p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) + ζ (D.mtp t, a) := by
  simp [phE, collapseExponent, tpE]

theorem phE_eq_sum (p : ℕ) (ζ : D.EM) : D.phE p ζ = ζ.sum fun x k => k • D.varE p x := by
  classical
  ext ⟨i, a⟩
  rw [Finsupp.sum_fintype _ _ (by intro x; simp), Finsupp.finsetSum_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rcases i with b | t
  · rw [phE_apply_inl]
    simp [varE, Finsupp.single_apply, mb, ite_and]
  · rw [phE_apply_inr]
    simp only [varE, Sum.elim_inl, Sum.elim_inr, Finsupp.smul_apply, Finsupp.single_apply, Prod.mk.injEq,
      Sum.inr.injEq, reduceCtorEq, false_and, if_false, Finset.sum_const_zero, zero_add,
      ite_and, smul_eq_mul, mul_ite, mul_one, mul_zero, mlab, mw, mtp]
    have key : ∀ f : D.Tau → Fin D.r → ℕ,
        (∑ x, ∑ y, if x = t then (if y = a then f x y else 0) else 0) = f t a := by
      intro f
      rw [Finset.sum_eq_single t (by intro x _ hx; simp [hx]) (by simp)]
      simp
    rw [key, key, key]
    ring

theorem ph_monomial (p : ℕ) (ζ : D.EM) (c : K) :
    D.ph p (monomial ζ c) = monomial (D.phE p ζ) c := by
  classical
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, phE_eq_sum]
  simp only [map_pow, ph_X, monomial_pow, one_pow]
  rw [show D.ph p (C c) = C c from (D.ph p).commutes c]
  rw [Finsupp.sum, ← monomial_sum_one, C_mul_monomial, mul_one]

theorem ldeg_phE (p : ℕ) (ζ : D.EM) (h : D.GoodE p ζ) (i : D.OL) : ldeg (D.phE p ζ) i = D.dO i := by
  obtain ⟨-, -, h3, h4, -⟩ := h
  rcases i with b | t
  · simp only [ldeg, phE_apply_inl, dO, Sum.elim_inl]
    exact h3 b
  · simp only [ldeg, phE_apply_inr, dO, Sum.elim_inr, Finset.sum_add_distrib, ← Finset.mul_sum]
    exact h4 t

theorem Good.add {p : ℕ} {Z W : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (hW : D.Good p W) :
    D.Good p (Z + W) := by
  classical
  intro ζ hζ
  rcases Finset.mem_union.mp (support_add hζ) with h | h
  · exact hZ ζ h
  · exact hW ζ h

theorem Good.smul {p : ℕ} {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (a : K) :
    D.Good p (a • Z) := fun ζ hζ => hZ ζ (support_smul hζ)

theorem Good.zero (p : ℕ) : D.Good p (0 : MvPolynomial (D.ML × Fin D.r) K) := by
  intro ζ hζ; simp at hζ

theorem Good.sum {p : ℕ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (D.ML × Fin D.r) K)
    (h : ∀ i ∈ s, D.Good p (f i)) : D.Good p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good.zero D p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Good.add D (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Good.monomial {p : ℕ} {ζ : D.EM} (h : D.GoodE p ζ) (c : K) : D.Good p (monomial ζ c) := by
  classical
  intro ζ' hζ'
  have := support_monomial_subset hζ'
  rw [Finset.mem_singleton] at this
  rw [this]; exact h

end TwistData

end Formalism.MainNotions.PlaneGram
