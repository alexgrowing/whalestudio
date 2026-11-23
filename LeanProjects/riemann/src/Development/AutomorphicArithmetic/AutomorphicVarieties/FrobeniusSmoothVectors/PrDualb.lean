import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_dualb :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Ideal C) (κ : Type) [Fintype κ] (ε : κ → C), maximalIdeal C * K = ⊥ → K = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) → ∃ co : κ → K →ₗ[O] ResidueField O, ∀ y : K, ∃ a : κ → O, (∀ u, residue O (a u) = co u y) ∧ (y : C) = ∑ u, a u • ε u := by
  intro O _ _ C _ _ _ K κ _ ε hK hspan hind
  have hε : ∀ u, ε u ∈ K := fun u => by
    rw [hspan]; exact Ideal.subset_span ⟨u, rfl⟩
  have hex : ∀ y : K, ∃ a : κ → O, (y : C) = ∑ u, a u • ε u := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Ideal.span (Set.range ε) := hspan ▸ hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy'
    choose a ha using fun u => IsCO.res_surj (O := O) (c u)
    refine ⟨a, ?_⟩
    show y = _
    rw [← hc]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h0 : (c u - algebraMap O C (a u)) * ε u ∈ maximalIdeal C * K :=
      Ideal.mul_mem_mul (ha u) (hε u)
    rw [hK, Ideal.mem_bot, sub_mul, sub_eq_zero] at h0
    rw [h0, Algebra.smul_def]
  have huniq : ∀ a b : κ → O, ∑ u, a u • ε u = ∑ u, b u • ε u →
      ∀ u, residue O (a u) = residue O (b u) := by
    intro a b hab u
    have h := hind (fun u => a u - b u) (by
      simp only [sub_smul, Finset.sum_sub_distrib, hab, sub_self]) u
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact h
  choose a ha using hex
  refine ⟨fun u =>
    { toFun := fun y => residue O (a y u)
      map_add' := fun x y => ?_
      map_smul' := fun c x => ?_ }, fun y => ⟨a y, fun u => rfl, ha y⟩⟩
  · rw [← map_add]
    refine huniq (a (x + y)) (fun u => a x u + a y u) ?_ u
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← ha, ← ha, ← ha]
    rfl
  · have h := huniq (a (c • x)) (fun u => c * a x u) (by
      simp only [mul_smul, ← Finset.smul_sum]
      rw [← ha, ← ha]
      rfl) u
    rw [h, RingHom.id_apply, map_mul, Algebra.smul_def]
    rfl
