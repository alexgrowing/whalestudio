import Mathlib

private theorem aux {ι : Type*} [DecidableEq ι] (t : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ t, f i ≠ 0) (j : ℕ) (hj : j ≤ t.card) :
    (t.val.map (fun i => (f i)⁻¹)).esymm j * (t.val.map f).prod
      = (t.val.map f).esymm (t.card - j) := by
  rw [Finset.esymm_map_val, Finset.esymm_map_val, Finset.sum_mul]
  refine Finset.sum_nbij' (fun u => t \ u) (fun u => t \ u) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_powersetCard] at hu ⊢
    exact ⟨Finset.sdiff_subset, by rw [Finset.card_sdiff_of_subset hu.1, hu.2]⟩
  · intro u hu
    rw [Finset.mem_powersetCard] at hu ⊢
    exact ⟨Finset.sdiff_subset, by rw [Finset.card_sdiff_of_subset hu.1, hu.2]; omega⟩
  · intro u hu
    rw [Finset.mem_powersetCard] at hu
    exact Finset.sdiff_sdiff_eq_self hu.1
  · intro u hu
    rw [Finset.mem_powersetCard] at hu
    exact Finset.sdiff_sdiff_eq_self hu.1
  · intro u hu
    rw [Finset.mem_powersetCard] at hu
    have h1 : (t.val.map f).prod = (∏ i ∈ t \ u, f i) * ∏ i ∈ u, f i :=
      (Finset.prod_sdiff hu.1).symm
    have h2 : (∏ i ∈ u, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi => hf i (hu.1 hi)
    rw [h1, Finset.prod_inv_distrib]
    field_simp

theorem UpperTheory.Reformulated.B.EsymmMapInvMulProd.esymm_inv :
    ∀ (s : Multiset ℂ),
    (∀ x ∈ s, x ≠ (0 : ℂ)) →
      ∀ j ≤ s.card, (Multiset.map (fun (x : ℂ) ↦ x⁻¹) s).esymm j * s.prod = s.esymm (s.card - j) := by
  intro s hs j hj
  classical
  have e : (Finset.univ : Finset s.ToType).val.map (fun x : s.ToType => (x : ℂ)) = s :=
    Multiset.map_univ_coe s
  have c : (Finset.univ : Finset s.ToType).card = s.card := by
    rw [Finset.card_univ, Multiset.card_coe]
  have h := aux (Finset.univ : Finset s.ToType) (fun x : s.ToType => (x : ℂ))
    (fun i _ => hs _ (Multiset.coe_mem)) j (by rw [c]; exact hj)
  have e2 : (Finset.univ : Finset s.ToType).val.map (fun x : s.ToType => ((x : ℂ))⁻¹)
      = s.map (fun x : ℂ => x⁻¹) := by
    conv_rhs => rw [← e]
    rw [Multiset.map_map]
    rfl
  rw [e2, e, c] at h
  exact h
