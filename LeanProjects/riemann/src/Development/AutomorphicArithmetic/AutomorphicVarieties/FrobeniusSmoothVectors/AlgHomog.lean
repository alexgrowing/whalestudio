import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem UpperTheory.V.Fr.single_coeff_mul {K : Type} [CommRing K] (p q : AddMonoidAlgebra K ℤ) (j : ℤ) :
    AddMonoidAlgebra.single j ((p * q).coeff j) = ∑ a ∈ p.coeff.support,
      AddMonoidAlgebra.single a (p.coeff a) * AddMonoidAlgebra.single (-a + j) (q.coeff (-a + j)) := by
  classical
  have key : ∀ a : ℤ, AddMonoidAlgebra.single a (p.coeff a) *
      AddMonoidAlgebra.single (-a + j) (q.coeff (-a + j)) =
        AddMonoidAlgebra.single j (p.coeff a * q.coeff (-a + j)) := by
    intro a
    rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel_left]
  simp_rw [key]
  have hc : (p * q).coeff j = ∑ a ∈ p.coeff.support, p.coeff a * q.coeff (-a + j) := by
    rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.sum]
    have hcond : ∀ b : ℤ, (a + b = j) ↔ (b = -a + j) := fun b => by omega
    simp_rw [hcond]
    rw [Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [Finsupp.notMem_support_iff.mp hm, mul_zero]
  rw [hc]
  ext k
  simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.finset_sum_apply,
    Finsupp.single_apply]
  split_ifs with hk
  · rfl
  · simp

theorem UpperTheory.V.Fr.alg_homog :
    ∀ {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K] {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (N : ℕ) (p : lauSub P), p ∈ vertex h ^ N → ∀ j : ℤ, (⟨AddMonoidAlgebra.single j (p.1.coeff j), single_mem_lauSub P (p.2 j)⟩ : lauSub P) ∈ vertex h ^ N := by
  intro C K _ _ _ _ P _ h N
  let comp : lauSub P → ℤ → lauSub P := fun q k =>
    ⟨AddMonoidAlgebra.single k (q.1.coeff k), single_mem_lauSub P (q.2 k)⟩
  have hcomp : ∀ q k, (comp q k).1 = AddMonoidAlgebra.single k (q.1.coeff k) := fun _ _ => rfl
  have base : ∀ q : lauSub P, q ∈ vertex h → ∀ k : ℤ, comp q k ∈ vertex h := by
    intro q hq k
    rw [mem_vertex] at hq ⊢
    obtain ⟨c, hc, hce⟩ := hq
    rw [hcomp, AddMonoidAlgebra.coeff_single]
    by_cases hk : k = 0
    · subst hk
      exact ⟨c, hc, by rw [Finsupp.single_eq_same, hce]⟩
    · exact ⟨0, Ideal.zero_mem _, by rw [Finsupp.single_eq_of_ne' hk, map_zero]⟩
  show ∀ p : lauSub P, p ∈ vertex h ^ N → ∀ j, comp p j ∈ vertex h ^ N
  induction N with
  | zero =>
    intro p _ j
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    intro p hp
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on (C := fun r => ∀ j, comp r j ∈ vertex h ^ (n + 1)) hp ?_ ?_
    · intro x hx y hy j
      have e : comp (x * y) j =
          ∑ a ∈ x.1.coeff.support, comp x a * comp y (-a + j) := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finset_sum, hcomp, Subalgebra.coe_mul, single_coeff_mul]
        rfl
      rw [e, pow_succ]
      exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih x hx a) (base y hy _)
    · intro x y hx hy j
      have e : comp (x + y) j = comp x j + comp y j := by
        apply Subtype.ext
        simp only [hcomp, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
          AddMonoidAlgebra.single_add]
      rw [e]
      exact add_mem (hx j) (hy j)
