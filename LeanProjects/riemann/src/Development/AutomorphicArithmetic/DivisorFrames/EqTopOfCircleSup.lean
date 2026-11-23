import Mathlib
open Filter Topology

theorem UpperTheory.eq_top_of_circle_sup :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (M : Subgroup G), IsClosed (M : Set G) →
        (∀ μ : G →* Circle, Continuous μ → (∀ m ∈ M, μ m = 1) → μ = 1) →
        ∀ c : Circle →* G, Continuous c → M ⊔ c.range = ⊤ → M = ⊤ := by
  intro G _ _ _ M hM hμ c hc hsup
  let S : AddSubgroup ℝ :=
    { carrier := {t | c (Circle.exp t) ∈ M}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Circle.exp_add, map_mul] at *
        exact M.mul_mem ha hb
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq, Circle.exp_neg, map_inv] at *
        exact M.inv_mem ha }
  have hSmem : ∀ t, t ∈ S ↔ c (Circle.exp t) ∈ M := fun t => Iff.rfl
  have hScl : IsClosed (S : Set ℝ) := hM.preimage (hc.comp Circle.exp.continuous)
  rcases S.dense_or_cyclic with hd | ⟨a, ha⟩
  · have hall : (S : Set ℝ) = Set.univ := by rw [← hScl.closure_eq, hd.closure_eq]
    rw [← hsup]
    refine (sup_eq_left.2 ?_).symm
    rintro _ ⟨z, rfl⟩
    obtain ⟨t, rfl⟩ := Circle.exp_surjective z
    have : t ∈ (S : Set ℝ) := by rw [hall]; trivial
    exact this
  · exfalso
    have h2 : (2 * Real.pi) ∈ S := by rw [hSmem]; simp
    rw [ha, AddSubgroup.mem_closure_singleton] at h2
    obtain ⟨n, hn⟩ := h2
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp only [zero_smul] at hn
      have := Real.pi_pos
      linarith
    haveI : IsClosed (M : Set G) := hM
    let f : Circle →* G ⧸ M := (QuotientGroup.mk' M).comp c
    have hfc : Continuous f := QuotientGroup.continuous_mk.comp hc
    have hfs : Function.Surjective f := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : g ∈ M ⊔ c.range := by rw [hsup]; trivial
      obtain ⟨m, hm, _, ⟨z, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hg
      refine ⟨z, ?_⟩
      simp [f, (QuotientGroup.eq_one_iff m).2 hm]
    have hq : IsQuotientMap f := hfc.isClosedMap.isQuotientMap hfc hfs
    have hker : f.ker ≤ (zpowGroupHom n : Circle →* Circle).ker := by
      intro z hz
      obtain ⟨t, rfl⟩ := Circle.exp_surjective z
      have ht : t ∈ S := by
        rw [hSmem]
        exact (QuotientGroup.eq_one_iff _).1 hz
      rw [ha, AddSubgroup.mem_closure_singleton] at ht
      obtain ⟨k, rfl⟩ := ht
      rw [MonoidHom.mem_ker, zpowGroupHom_apply, ← Circle.exp_intCast_mul, Circle.exp_eq_one]
      refine ⟨k, ?_⟩
      rw [← hn]
      simp only [zsmul_eq_mul]
      ring
    let φ : G ⧸ M →* Circle := f.liftOfSurjective hfs ⟨zpowGroupHom n, hker⟩
    have hφ : ∀ z, φ (f z) = z ^ n := fun z =>
      f.liftOfRightInverse_comp_apply _ _ _ z
    have hφc : Continuous φ := by
      rw [hq.continuous_iff]
      have : (φ ∘ f) = fun z => z ^ n := funext hφ
      rw [this]
      exact continuous_zpow n
    have h1 := hμ (φ.comp (QuotientGroup.mk' M)) (hφc.comp QuotientGroup.continuous_mk) (by
      intro m hm
      simp [(QuotientGroup.eq_one_iff m).2 hm])
    have h3 : (Circle.exp (Real.pi / n)) ^ n = 1 := by
      rw [← hφ]
      exact DFunLike.congr_fun h1 (c (Circle.exp (Real.pi / n)))
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    rw [← Circle.exp_intCast_mul, mul_div_cancel₀ _ hn'] at h3
    exact Circle.exp_pi_ne_one h3
