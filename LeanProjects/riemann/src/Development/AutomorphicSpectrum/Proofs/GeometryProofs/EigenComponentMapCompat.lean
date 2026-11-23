import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigMap

open GlobalTheory.CompanionTheory.Ar

section Indep

variable {k V O : Type} [Field k] [AddCommGroup V] [Module k V] [CommRing O]

theorem mem_eigSp_iff' (ρ : O →+* Module.End k V) (σ : O →+* k) (x : V) :
    x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem eigSp_sum_eq_zero (ρ : O →+* Module.End k V) (s : Finset (O →+* k)) :
    ∀ f : (O →+* k) → V, (∀ t ∈ s, f t ∈ eigSp ρ t) → ∑ t ∈ s, f t = 0 → ∀ t ∈ s, f t = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert t₀ s ht₀ ih =>
    intro f hf hsum
    have hf' : ∀ t ∈ s, f t ∈ eigSp ρ t := fun t ht => hf t (Finset.mem_insert_of_mem ht)
    have hf₀ := (mem_eigSp_iff' ρ t₀ _).1 (hf t₀ (Finset.mem_insert_self _ _))
    rw [Finset.sum_insert ht₀] at hsum
    have hs : ∀ t ∈ s, f t = 0 := by
      intro t ht
      have hne : t ≠ t₀ := fun e => ht₀ (e ▸ ht)
      obtain ⟨a, ha⟩ : ∃ a, t a ≠ t₀ a := by
        by_contra hcon
        push_neg at hcon
        exact hne (RingHom.ext hcon)
      have hz : ∑ u ∈ s, (u a - t₀ a) • f u = 0 := by
        have h1 : ρ a (f t₀ + ∑ u ∈ s, f u) - t₀ a • (f t₀ + ∑ u ∈ s, f u) = 0 := by
          rw [hsum]; simp
        have h2 : ρ a (∑ u ∈ s, f u) = ∑ u ∈ s, u a • f u := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun u hu => (mem_eigSp_iff' ρ u _).1 (hf' u hu) a
        rw [map_add, hf₀ a, h2, smul_add, Finset.smul_sum] at h1
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← h1]
        abel
      have := ih (fun u => (u a - t₀ a) • f u)
        (fun u hu => Submodule.smul_mem _ _ (hf' u hu)) hz t ht
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha)
    have h₀ : f t₀ = 0 := by
      rw [Finset.sum_eq_zero hs, add_zero] at hsum
      exact hsum
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact h₀
    · exact hs t ht

theorem iSupIndep_eigSp (ρ : O →+* Module.End k V) : iSupIndep (fun σ : O →+* k => eigSp ρ σ) :=
  (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero _).2 fun s v hv h0 i hi =>
    eigSp_sum_eq_zero ρ s v hv h0 i hi

theorem eq_zero_of_mem_eigSp_of_mem_iSup (ρ : O →+* Module.End k V) (σ : O →+* k) {y : V}
    (h₁ : y ∈ eigSp ρ σ) (h₂ : y ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ') : y = 0 :=
  Submodule.disjoint_def.1 (iSupIndep_eigSp ρ σ) y h₁ (by simpa using h₂)

end Indep

theorem eigComp_map {k k' V V' O : Type} [Field k] [Field k'] [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k' V'] [CommRing O] (κ : k →+* k') (j : V →+ V') (hj : ∀ (c : k) x, j (c • x) = κ c • j x)
    (ρ : O →+* Module.End k V) (ρ' : O →+* Module.End k' V') (hρ : ∀ a x, ρ' a (j x) = j (ρ a x))
    (σ : O →+* k) (x : V) (hx : eigComp ρ σ x ≠ 0) :
    eigComp ρ' (κ.comp σ) (j x) = j (eigComp ρ σ x) := by
  have hmap : ∀ (s : O →+* k) (y : V), y ∈ eigSp ρ s → j y ∈ eigSp ρ' (κ.comp s) := by
    intro s y hy
    refine (mem_eigSp_iff' ρ' _ _).2 fun a => ?_
    rw [hρ, (mem_eigSp_iff' ρ s y).1 hy a, hj]
    rfl
  have hsup : ∀ y ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ',
      j y ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ' := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y =>
      j y ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ') hy ?_ (by simp) ?_
    · intro s y hy
      refine Submodule.iSup_induction _ (motive := fun y =>
        j y ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ') hy ?_ (by simp) ?_
      · intro hs y hy
        have hne : κ.comp s ≠ κ.comp σ := fun e => hs (RingHom.ext fun a =>
          κ.injective (RingHom.congr_fun e a))
        exact Submodule.mem_iSup_of_mem (κ.comp s) (Submodule.mem_iSup_of_mem hne (hmap s y hy))
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  have h : ∃ p ∈ eigSp ρ σ, x - p ∈ ⨆ σ' ∈ {σ' : O →+* k | σ' ≠ σ}, eigSp ρ σ' := by
    by_contra hcon
    exact hx (by rw [eigComp, dif_neg hcon])
  have hp : eigComp ρ σ x = h.choose := by rw [eigComp, dif_pos h]
  obtain ⟨hp₁, hp₂⟩ := h.choose_spec
  rw [← hp] at hp₁ hp₂
  have hp₃ := hsup _ hp₂
  rw [map_sub] at hp₃
  have h' : ∃ q ∈ eigSp ρ' (κ.comp σ), j x - q ∈ ⨆ τ' ∈ {τ' : O →+* k' | τ' ≠ κ.comp σ}, eigSp ρ' τ' :=
    ⟨_, hmap σ _ hp₁, hp₃⟩
  have hq : eigComp ρ' (κ.comp σ) (j x) = h'.choose := by rw [eigComp, dif_pos h']
  obtain ⟨hq₁, hq₂⟩ := h'.choose_spec
  rw [← hq] at hq₁ hq₂
  refine sub_eq_zero.1 (eq_zero_of_mem_eigSp_of_mem_iSup ρ' (κ.comp σ)
    (Submodule.sub_mem _ hq₁ (hmap σ _ hp₁)) ?_)
  have : eigComp ρ' (κ.comp σ) (j x) - j (eigComp ρ σ x) =
      (j x - j (eigComp ρ σ x)) - (j x - eigComp ρ' (κ.comp σ) (j x)) := by abel
  rw [this]
  exact Submodule.sub_mem _ hp₃ hq₂

end GlobalTheory.CompanionTheory.Ar.Cusp.EigMap
