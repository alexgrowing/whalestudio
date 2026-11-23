import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
open NumberField

namespace PositivityTheory.Xgf

theorem exists_nsmul_mem_span_full_family {E : Type} [Field E] [NumberField E] {M : Type} [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] {I : Type} [Fintype I] (e : I → M)
    (hcard : Fintype.card I = Module.finrank (𝓞 E) M) (he : LinearIndependent (𝓞 E) e) :
    ∃ n : ℕ, 0 < n ∧ ∀ y : M, n • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
  classical
  set N := Submodule.span (𝓞 E) (Set.range e) with hN
  have htor : ∀ y : M, ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ N := by
    intro y
    have hnot : ¬ LinearIndependent (𝓞 E) (Sum.elim e (fun _ : Unit => y)) := by
      intro hli
      have := hli.fintype_card_le_finrank
      rw [Fintype.card_sum, Fintype.card_unit, hcard] at this
      omega
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton] at hg
    by_cases hc : g (Sum.inr ()) = 0
    · exfalso
      rw [hc, zero_smul, add_zero] at hg
      have h0 := Fintype.linearIndependent_iff.mp he (fun j => g (Sum.inl j)) hg
      rcases i with j | ⟨⟩
      · exact hi (h0 j)
      · exact hi hc
    · refine ⟨g (Sum.inr ()), hc, ?_⟩
      rw [eq_neg_of_add_eq_zero_right hg]
      exact N.neg_mem (N.sum_mem fun j _ => N.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩))
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M)
  choose c hc0 hcN using htor
  have ha0 : (∏ y ∈ s, c y) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun y _ => hc0 y
  have haN : ∀ y : M, (∏ y ∈ s, c y) • y ∈ N := by
    intro y
    have hy : y ∈ Submodule.span (𝓞 E) (s : Set M) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
        rw [← Finset.prod_erase_mul s c hx, mul_smul]
        exact N.smul_mem _ (hcN x)
    | zero => simp
    | add x z _ _ hx hz => rw [smul_add]; exact N.add_mem hx hz
    | smul b x _ hx => rw [smul_comm]; exact N.smul_mem b hx
  have hI : Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  refine ⟨Ideal.absNorm (Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E))),
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y => ?_⟩
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span ({∏ y ∈ s, c y} : Set (𝓞 E))))
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hb, mul_smul]
  exact N.smul_mem b (haN y)

end PositivityTheory.Xgf
