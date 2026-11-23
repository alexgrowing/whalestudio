import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

open MvPolynomial

theorem is_c1_of_finite_of_tsen_lang_systems : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K],
  (∀ (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) F), (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0) → IsFirstChernClassOfLineBundle K := by
  intro F K _ _ _ _ hF n d f hf hd hdn
  set m := Module.finrank F K with hm
  have hm0 : 0 < m := Module.finrank_pos
  let b : Module.Basis (Fin m) F K := Module.finBasis F K
  let e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv
  let g : Fin n → MvPolynomial (Fin (n * m)) K := fun i => ∑ j, MvPolynomial.C (b j) * MvPolynomial.X (e (i, j))
  have hg : ∀ i, (g i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)
  let G : MvPolynomial (Fin (n * m)) K := aeval g f
  have hG : G.IsHomogeneous d := by
    have h1 := hf.aeval g hg
    rwa [one_mul] at h1
  let P : Fin m → MvPolynomial (Fin (n * m)) F := fun l =>
    ∑ s ∈ G.support, monomial s (b.repr (G.coeff s) l)
  have hP : ∀ l, (P l).IsHomogeneous d := fun l =>
    IsHomogeneous.sum _ _ _ (fun s hs => isHomogeneous_monomial _ (by
      rw [Finsupp.degree_eq_weight_one]; exact hG (mem_support_iff.mp hs)))
  have hlt : m * d < n * m := by
    rw [mul_comm n m]; exact Nat.mul_lt_mul_of_pos_left hdn hm0
  obtain ⟨y, hy0, hy⟩ := hF (n * m) m d P hP hd hlt
  let x : Fin n → K := fun i => ∑ j, algebraMap F K (y (e (i, j))) * b j
  refine ⟨x, ?_, ?_⟩
  · intro hx
    apply hy0
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective k
    have hxi : ∑ j, y (e (i, j)) • b j = 0 := by
      have := congrFun hx i
      simpa [x, Algebra.smul_def] using this
    exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => y (e (i, j))) hxi j
  · have key : MvPolynomial.eval x f = MvPolynomial.eval (fun k => algebraMap F K (y k)) G := by
      rw [← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
      show _ = MvPolynomial.aeval _ (MvPolynomial.bind₁ g f)
      rw [MvPolynomial.aeval_bind₁]
      have hxe : x = fun i => MvPolynomial.aeval (fun k => algebraMap F K (y k)) (g i) := by
        funext i
        simp [g, x, mul_comm]
      rw [hxe]
      rfl
    have key2 : MvPolynomial.eval (fun k => algebraMap F K (y k)) G
        = ∑ l, algebraMap F K (MvPolynomial.eval y (P l)) * b l := by
      simp only [P, map_sum, MvPolynomial.eval_monomial, Finset.sum_mul]
      rw [Finset.sum_comm, MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      conv_lhs => rw [← b.sum_repr (G.coeff s)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp [Finsupp.prod, map_prod, map_pow, Algebra.smul_def]
      ring
    rw [key, key2]
    exact Finset.sum_eq_zero (fun l _ => by rw [hy l, map_zero, zero_mul])

end GlobalTheory
