import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

namespace GlobalTheory.UnrLoc

theorem fixed_ne_bot_of_mem_iSup_range :
    ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
      {ι : Type} [Finite ι] {σ : Representation ℂ G V}, σ.IsIrreducible →
      ∀ {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X},
      f ∈ ⨆ j, LinearMap.range (T j).toLinearMap → f ≠ 0 → (∀ k ∈ K, ρ k f = f) →
      GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
  intro G V X _ _ _ _ _ ι _ σ hσ ρ T K f hf hf0 hfix
  classical
  haveI : IsSimpleOrder (Subrepresentation σ) := hσ
  haveI : Fintype ι := Fintype.ofFinite ι

  let Y : Finset ι → Submodule ℂ X := fun t => ⨆ j ∈ t, LinearMap.range (T j).toLinearMap
  have hYst : ∀ (t : Finset ι) (g : G) (x : X), x ∈ Y t → ρ g x ∈ Y t := by
    intro t g x hx
    have hle : Y t ≤ (Y t).comap (ρ g) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      have : ρ g ((T j).toLinearMap v) = (T j).toLinearMap (σ g v) := by
        simp only [Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining]
      rw [this]
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => LinearMap.range (T j).toLinearMap) j hj)
        (LinearMap.mem_range_self _ _)
    exact hle hx
  have key : ∀ (t : Finset ι) (x : X), x ∈ Y t → x ≠ 0 → (∀ k ∈ K, ρ k x = x) →
      GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx hx0 _
      exact absurd (by simpa [Y] using hx) hx0
    | insert j t hjt ih =>
      intro x hx hx0 hxfix
      have hx' : x ∈ LinearMap.range (T j).toLinearMap ⊔ Y t := by
        simpa [Y, Finset.iSup_insert] using hx
      obtain ⟨y, ⟨v, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      let U : Subrepresentation σ :=
        ⟨(Y t).comap (T j).toLinearMap, fun g w hw => by
          rw [Submodule.mem_comap] at hw ⊢
          have : (T j).toLinearMap (σ g w) = ρ g ((T j).toLinearMap w) := by
            simp only [Representation.IntertwiningMap.toLinearMap_apply,
              Representation.IntertwiningMap.isIntertwining]
          rw [this]
          exact hYst t g _ hw⟩
      rcases eq_bot_or_eq_top U with hU | hU
      · have hU' : (Y t).comap (T j).toLinearMap = ⊥ := congrArg Subrepresentation.toSubmodule hU
        have hvfix : ∀ k ∈ K, σ k v = v := by
          intro k hk
          have hmem : σ k v - v ∈ (Y t).comap (T j).toLinearMap := by
            rw [Submodule.mem_comap, map_sub]
            have h1 := hxfix k hk
            have h2 : (T j).toLinearMap (σ k v) = ρ k ((T j).toLinearMap v) := by
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.IntertwiningMap.isIntertwining]
            rw [map_add] at h1
            have h3 : (T j).toLinearMap (σ k v) - (T j).toLinearMap v = z - ρ k z := by
              rw [h2, sub_eq_sub_iff_add_eq_add, h1, add_comm]
            rw [h3]
            exact sub_mem hz (hYst t k z hz)
          rw [hU'] at hmem
          exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hmem)
        by_cases hv : v = 0
        · subst hv
          simp only [map_zero, zero_add] at hx0 hxfix hz ⊢
          exact ih z hz hx0 hxfix
        · rw [Submodule.ne_bot_iff]
          refine ⟨v, ?_, hv⟩
          intro h
          simp [hvfix _ h.2]
      · have hv : (T j).toLinearMap v ∈ Y t := by
          have : v ∈ (⊤ : Subrepresentation σ).toSubmodule := Submodule.mem_top
          rw [← hU] at this
          exact this
        exact ih _ (add_mem hv hz) hx0 hxfix
  refine key Finset.univ f ?_ hf0 hfix
  simpa [Y] using hf

end GlobalTheory.UnrLoc
