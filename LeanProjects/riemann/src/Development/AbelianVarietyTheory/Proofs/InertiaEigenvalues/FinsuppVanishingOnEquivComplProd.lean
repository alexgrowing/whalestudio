import Mathlib

namespace GlobalTheory

theorem finsupp_vanishing_on_equiv_compl_prod :
    ∀ {I : Type} (S : Finset I) (n : ℕ),
    ∃ e : {l : I →₀ (Fin n → ℤ) // ∀ v ∈ S, l v = 0} ≃ ({i : I // i ∉ S} →₀ (Fin n → ℤ)),
      ∀ (M : Type) [CommMonoid M] (r : I → (Fin n → ℤ) → M), (∀ i, r i 0 = 1) →
        ∀ l, (e l).prod (fun i v => r i.1 v) = l.1.prod r := by
  intro I S n
  classical
  refine ⟨{
    toFun := fun l => l.1.subtypeDomain (· ∉ S)
    invFun := fun l' => ⟨l'.embDomain (Function.Embedding.subtype _), by
      intro v hv
      apply Finsupp.embDomain_notin_range
      rintro ⟨i, rfl⟩
      exact i.2 hv⟩
    left_inv := by
      rintro ⟨l, hl⟩
      apply Subtype.ext
      refine Finsupp.ext fun v => ?_
      by_cases hv : v ∈ S
      · show Finsupp.embDomain _ _ v = l v
        rw [Finsupp.embDomain_notin_range, hl v hv]
        rintro ⟨i, rfl⟩
        exact i.2 hv
      · show Finsupp.embDomain _ _ v = l v
        have := Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∉ S))
          (l.subtypeDomain (· ∉ S)) ⟨v, hv⟩
        simpa using this
    right_inv := by
      intro l'
      refine Finsupp.ext fun i => ?_
      rw [Finsupp.subtypeDomain_apply]
      exact Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∉ S)) l' i }, ?_⟩
  intro M _ r _ l
  obtain ⟨l, hl⟩ := l
  show (l.subtypeDomain (· ∉ S)).prod (fun i v => r i.1 v) = l.prod r
  apply Finsupp.prod_subtypeDomain_index
  intro x hx hxS
  exact (Finsupp.mem_support_iff.mp hx) (hl x hxS)

end GlobalTheory
