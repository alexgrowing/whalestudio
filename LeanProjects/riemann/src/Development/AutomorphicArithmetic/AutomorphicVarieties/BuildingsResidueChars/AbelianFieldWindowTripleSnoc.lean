import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs

open Module in
theorem UpperTheory.abelianField_window_triple_snoc :
    UpperTheory.V.Af.Wd.TriSnoc := by
  unfold UpperTheory.V.Af.Wd.TriSnoc
  intro k W' W W'' ι _ _ _ _ _ _ _ n T' T T'' f p hf hp hex h1 hT' hT'' d hd hd''
  unfold UpperTheory.V.Af.Wd.IsTri at hd ⊢
  obtain ⟨b', hb'⟩ := hd
  obtain ⟨y, hy0, hyspan⟩ := (finrank_eq_one_iff').1 h1
  obtain ⟨s, hs⟩ := hp y
  have hrange : Submodule.span k (Set.range fun i => f (b' i)) ≤ LinearMap.ker p := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (hex _).2 ⟨_, rfl⟩
  have hli : LinearIndependent k (Fin.snoc (fun i => f (b' i)) s : Fin (n + 1) → W) := by
    rw [linearIndependent_fin_snoc]
    refine ⟨b'.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
    intro hmem
    have h0 : p s = 0 := LinearMap.mem_ker.1 (hrange hmem)
    rw [hs] at h0
    exact hy0 h0
  have hsp : ⊤ ≤ Submodule.span k (Set.range (Fin.snoc (fun i => f (b' i)) s : Fin (n + 1) → W)) := by
    intro w _
    obtain ⟨c, hc⟩ := hyspan (p w)
    have hker : p (w - c • s) = 0 := by rw [map_sub, map_smul, hs, hc, sub_self]
    obtain ⟨x, hx⟩ := (hex _).1 hker
    have hw : w = f x + c • s := by rw [hx]; abel
    rw [hw]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last n, by simp⟩))
    rw [← b'.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.castSucc, by simp⟩)
  set b := Module.Basis.mk hli hsp with hbdef
  have hbc : ∀ i, b i.castSucc = f (b' i) := fun i => by simp [b]
  have hbl : b (Fin.last n) = s := by simp [b]
  have hfx : ∀ x : W', f x = ∑ i, (b'.repr x i) • b i.castSucc := by
    intro x
    conv_lhs => rw [← b'.sum_repr x]
    rw [map_sum]
    simp only [map_smul, hbc]
  have hrepr1 : ∀ (x : W') (i : Fin n), b.repr (f x) i.castSucc = b'.repr x i := by
    intro x i
    rw [hfx]
    simp [map_sum, Finsupp.single_apply, Fin.castSucc_inj]
  have hrepr2 : ∀ x : W', b.repr (f x) (Fin.last n) = 0 := by
    intro x
    rw [hfx]
    simp [map_sum, Finsupp.single_apply]
  refine ⟨b, fun a => ⟨?_, ?_⟩⟩
  · intro i j hji
    rw [LinearMap.toMatrix_apply]
    induction j using Fin.lastCases with
    | last => exact absurd hji (not_lt.2 (Fin.le_last i))
    | cast j =>
      rw [hbc, ← hT']
      induction i using Fin.lastCases with
      | last => exact hrepr2 _
      | cast i =>
        rw [hrepr1]
        have := (hb' a).1 i j (Fin.castSucc_lt_castSucc_iff.1 hji)
        rwa [LinearMap.toMatrix_apply] at this
  · intro i
    rw [LinearMap.toMatrix_apply]
    induction i using Fin.lastCases with
    | last =>
      rw [hbl]
      have hker : p (T a s - d a (Fin.last n) • s) = 0 := by
        rw [map_sub, map_smul, hT'', hs, hd'', sub_self]
      obtain ⟨x, hx⟩ := (hex _).1 hker
      have hTs : T a s = f x + d a (Fin.last n) • s := by rw [hx]; abel
      rw [hTs, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, hrepr2, ← hbl, b.repr_self]
      simp
    | cast i =>
      rw [hbc, ← hT', hrepr1]
      have := (hb' a).2 i
      rwa [LinearMap.toMatrix_apply] at this
