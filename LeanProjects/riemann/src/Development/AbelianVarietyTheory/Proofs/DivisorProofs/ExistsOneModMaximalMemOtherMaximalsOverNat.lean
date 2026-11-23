import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem GlobalTheory.sep_one_mod_maximal_mem_others : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 := by
  intro E _ _ n hn 𝔭 h𝔭
  have hn0 : (n : 𝓞 E) ≠ 0 := by exact_mod_cast hn.ne'
  have hI0 : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  set S := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(n : 𝓞 E)})).toFinset.erase 𝔭
    with hS
  have htop : 𝔭 ⊔ ∏ 𝔮 ∈ S, 𝔮 = ⊤ := by
    refine Ideal.sup_prod_eq_top fun 𝔮 h𝔮 => ?_
    rw [hS, Finset.mem_erase, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI0] at h𝔮
    obtain ⟨hne, hpr, hle⟩ := h𝔮
    have hbot : 𝔮 ≠ ⊥ := by
      rintro rfl
      rw [Ideal.span_le, Set.singleton_subset_iff] at hle
      exact hn0 hle
    have hmax : 𝔮.IsMaximal := hpr.isMaximal hbot
    by_contra hc
    have e1 : 𝔭 = 𝔭 ⊔ 𝔮 := h𝔭.eq_of_le hc le_sup_left
    have h2 : 𝔮 ≤ 𝔭 := e1 ▸ le_sup_right
    exact hne (hmax.eq_of_le h𝔭.ne_top h2)
  have h1 : (1 : 𝓞 E) ∈ 𝔭 ⊔ ∏ 𝔮 ∈ S, 𝔮 := htop ▸ Submodule.mem_top
  obtain ⟨p, hp, e, he, hpe⟩ := Submodule.mem_sup.mp h1
  refine ⟨e, ?_, fun 𝔮 hmax hn𝔮 hne => ?_⟩
  · have : e - 1 = -p := by rw [← hpe]; ring
    rw [this]; exact 𝔭.neg_mem hp
  · have hmem : 𝔮 ∈ S := by
      rw [hS, Finset.mem_erase, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hI0]
      exact ⟨hne, hmax.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hn𝔮⟩
    exact Ideal.prod_le_inf.trans (Finset.inf_le hmem) he
