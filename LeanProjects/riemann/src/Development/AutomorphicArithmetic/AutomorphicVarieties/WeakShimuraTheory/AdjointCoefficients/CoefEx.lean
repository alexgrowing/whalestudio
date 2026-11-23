import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.coefEx :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {A : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] (K : Ideal A), maximalIdeal A * K = ⊥ → ∀ (κ : Type) [Fintype κ] (ε : κ → A), K = Ideal.span (Set.range ε) → (∀ c : κ → Λ, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal Λ) → ∃ co : κ → A → ResidueField Λ, (∀ u, ∀ x ∈ K, ∀ y ∈ K, co u (x + y) = co u x + co u y) ∧ (∀ u (a : A), ∀ x ∈ K, co u (a * x) = res Λ A a * co u x) ∧ ∀ x ∈ K, ∃ a : κ → Λ, (∀ u, residue Λ (a u) = co u x) ∧ x = ∑ u, a u • ε u := by
  intro Λ _ _ A _ _ _ K hK κ _ ε hspan hind
  classical
  have hkill : ∀ m ∈ maximalIdeal A, ∀ e ∈ K, m * e = 0 := by
    intro m hm e he
    have h := Ideal.mul_mem_mul hm he
    rw [hK] at h
    exact (Submodule.mem_bot A).mp h
  have hsc : ∀ b : A, ∃ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A := fun b => IsCO.res_surj (O := Λ) b
  have hact : ∀ b : A, ∀ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A → ∀ e ∈ K, b * e = l • e := by
    intro b l hb e he
    have h := hkill _ hb e he
    rw [sub_mul] at h
    rw [Algebra.smul_def]
    exact sub_eq_zero.mp h
  have hres : ∀ b : A, ∀ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A → res Λ A b = residue Λ l := by
    intro b l hb
    have h := (res_eq_zero_iff Λ A _).mpr hb
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h
    rw [h]
    rfl
  have hex : ∀ x ∈ K, ∃ a : κ → Λ, x = ∑ u, a u • ε u := by
    intro x hx
    have hx' := hx
    rw [hspan] at hx'
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hx'
    choose l hl using fun u => hsc (b u)
    refine ⟨l, ?_⟩
    rw [← hb]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_eq_mul]
    refine hact _ _ (hl u) _ ?_
    rw [hspan]
    exact Ideal.subset_span ⟨u, rfl⟩
  have huniq : ∀ a a' : κ → Λ, ∑ u, a u • ε u = ∑ u, a' u • ε u →
      ∀ u, residue Λ (a u) = residue Λ (a' u) := by
    intro a a' h u
    have h0 := hind (a - a') (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]) u
    rw [← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).mpr h0
  let co : κ → A → ResidueField Λ := fun u x => if h : x ∈ K then residue Λ ((hex x h).choose u) else 0
  have hco : ∀ x (h : x ∈ K) (a : κ → Λ), x = ∑ u, a u • ε u → ∀ u, co u x = residue Λ (a u) := by
    intro x h a hx u
    simp only [co, dif_pos h]
    exact huniq _ _ ((hex x h).choose_spec.symm.trans hx) u
  refine ⟨co, ?_, ?_, ?_⟩
  · intro u x hx y hy
    obtain ⟨a, ha⟩ := hex x hx
    obtain ⟨b, hb⟩ := hex y hy
    rw [hco x hx a ha, hco y hy b hb, hco (x + y) (K.add_mem hx hy) (a + b)
      (by rw [ha, hb, ← Finset.sum_add_distrib]; simp [add_smul]), Pi.add_apply, map_add]
  · intro u c x hx
    obtain ⟨a, ha⟩ := hex x hx
    obtain ⟨l, hl⟩ := hsc c
    rw [hco x hx a ha, hco (c * x) (K.mul_mem_left c hx) (l • a) ?_, hres c l hl, Pi.smul_apply, smul_eq_mul,
      map_mul]
    rw [hact c l hl x hx, ha, Finset.smul_sum]
    simp [smul_smul]
  · intro x hx
    obtain ⟨a, ha⟩ := hex x hx
    exact ⟨a, fun u => (hco x hx a ha u).symm, ha⟩
