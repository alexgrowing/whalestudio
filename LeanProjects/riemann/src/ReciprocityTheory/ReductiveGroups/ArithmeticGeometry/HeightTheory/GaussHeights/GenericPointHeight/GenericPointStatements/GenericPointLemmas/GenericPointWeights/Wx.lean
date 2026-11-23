import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtLeafSt

open NumberField

namespace PI.HtGenericPt.Pf

theorem main {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A) : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.exists_generic 𝒜 d := by
  unfold ReciprocityTheory.ChartRestriction.G.T0.LeafSt.exists_generic
  intro hd h
  refine ⟨?_, ?_⟩
  · haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
    have hL : ∀ (c : ι) (x : Fin (d.N + 1) → K),
        ((LinearMap.proj c : ((c : ι) → A c) →ₗ[K] A c) ∘ₗ
          (∑ j, (LinearMap.proj j : (Fin (d.N + 1) → K) →ₗ[K] K).smulRight (d.w j))) x = d.wx x c := by
      intro c x
      simp [ReciprocityTheory.ChartRestriction.G.T0.Data.wx, LinearMap.sum_apply, Finset.sum_apply]
    have hne : ∀ c, LinearMap.ker ((LinearMap.proj c : ((c : ι) → A c) →ₗ[K] A c) ∘ₗ
        (∑ j, (LinearMap.proj j : (Fin (d.N + 1) → K) →ₗ[K] K).smulRight (d.w j))) ≠ ⊤ := by
      intro c htop
      have hmem : (Pi.single (d.jc c) 1 : Fin (d.N + 1) → K) ∈
          LinearMap.ker ((LinearMap.proj c : ((c : ι) → A c) →ₗ[K] A c) ∘ₗ
            (∑ j, (LinearMap.proj j : (Fin (d.N + 1) → K) →ₗ[K] K).smulRight (d.w j))) := by
        rw [htop]
        exact Submodule.mem_top
      rw [LinearMap.mem_ker, hL] at hmem
      apply hd.w_base c
      simpa [ReciprocityTheory.ChartRestriction.G.T0.Data.wx, Pi.single_apply, Finset.sum_apply, ite_apply, Pi.zero_apply,
        Finset.sum_ite_eq'] using hmem
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top _ hne
    refine ⟨x, fun c => ?_⟩
    have hxc := hx c
    rw [LinearMap.mem_ker, hL] at hxc
    exact hxc
  · obtain ⟨e, he, -⟩ := hd.a4
    exact ⟨e, he⟩

end PI.HtGenericPt.Pf
