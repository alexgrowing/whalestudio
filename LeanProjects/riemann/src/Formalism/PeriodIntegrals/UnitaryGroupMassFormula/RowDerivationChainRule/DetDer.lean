import Mathlib
import Formalism.PeriodIntegrals.RowLetter

open MvPolynomial

noncomputable section

namespace PI.RL.W

section General

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem derivation_finset_prod {ι : Type*} [DecidableEq ι] (D : Derivation R S S) (f : ι → S) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  have hne : ∀ i ∈ s, i ≠ a := fun i hi h => ha (h ▸ hi)
  have h0 : Function.update f a (D (f a)) a = D (f a) := by simp
  have h1 : ∏ j ∈ s, Function.update f a (D (f a)) j = ∏ j ∈ s, f j :=
    Finset.prod_congr rfl fun j hj => Function.update_of_ne (hne j hj) _ _
  have h2 : ∀ i ∈ s, ∏ j ∈ insert a s, Function.update f i (D (f i)) j =
      f a * ∏ j ∈ s, Function.update f i (D (f i)) j := fun i hi => by
    rw [Finset.prod_insert ha, Function.update_of_ne (hne i hi).symm]
  rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.prod_insert ha, h0, h1,
    Finset.sum_congr rfl h2, ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
  ring

theorem derivation_det {n : Type*} [Fintype n] [DecidableEq n] (D : Derivation R S S) (A : Matrix n n S) :
    D A.det = ∑ i, (A.updateRow i fun j => D (A i j)).det := by
  have key : ∀ B : Matrix n n S, B.det = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : S) * ∏ i, B i (σ i) :=
    fun B => by rw [← Matrix.det_transpose, Matrix.det_apply']; rfl
  have hc : ∀ k : ℤ, D (k : S) = 0 := fun k => by
    rw [← map_intCast (algebraMap R S) k, Derivation.map_algebraMap]
  have hrow : ∀ (i : n) (σ : Equiv.Perm n), ∏ j, (A.updateRow i fun j => D (A i j)) j (σ j) =
      ∏ j, Function.update (fun j => A j (σ j)) i (D (A i (σ i))) j := fun i σ =>
    Finset.prod_congr rfl fun j _ => by
      by_cases h : j = i
      · subst h; simp
      · simp [Matrix.updateRow_ne h, Function.update_of_ne h]
  rw [key, map_sum]
  simp_rw [key, hrow, Derivation.leibniz, hc, smul_zero, add_zero, derivation_finset_prod, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem derivation_sum_apply {ι : Type*} {A M : Type*} [CommSemiring A] [AddCommMonoid M] [Module A M]
    [Algebra R A] [Module R M] (s : Finset ι) (D : ι → Derivation R A M) (x : A) :
    (∑ t ∈ s, D t) x = ∑ t ∈ s, D t x := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

end General

def REder (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) :
    Derivation K (MvPolynomial (Fin k × Fin k) K) (MvPolynomial (Fin k × Fin k) K) :=
  ∑ t : Fin k, (X (a, t) : MvPolynomial (Fin k × Fin k) K) • pderiv (b, t)

theorem RE_eq_REder (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) :
    PI.RL.RE K k a b f = REder K k a b f := by
  unfold PI.RL.RE REder
  rw [derivation_sum_apply]
  rfl

theorem REder_X (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (i j : Fin k) :
    REder K k a b (X (i, j)) = if i = b then X (a, j) else 0 := by
  unfold REder
  rw [derivation_sum_apply]
  simp only [Derivation.smul_apply, pderiv_X, smul_eq_mul]
  by_cases h : i = b
  · subst h
    simp [Pi.single_apply, mul_ite]
  · simp [Pi.single_apply, h]

end PI.RL.W
