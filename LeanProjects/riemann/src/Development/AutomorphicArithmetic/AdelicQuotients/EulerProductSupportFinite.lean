import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

theorem UpperTheory.euler_product_support_finite :
    EulerSupp := by
  intro V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K T _ _ _ _ _ _ _ _
    Ti _ _ _ _ _ _ _ _ Tv _ _ _ _ _ _ _ _ qT pT KT hR hRT j ji jv hq hp hK S Fi Fv hFi hFii hFv hS
  classical
  have hKA : ∀ v x, x ∈ K v → ∃ t, ∃ y ∈ K v, x = jv v t * y :=
    fun v x hx => ⟨1, x, hx, by simp⟩
  have hfin : ∀ g, (Function.mulSupport fun v => Fv v (p v g)).Finite := by
    intro g
    refine ((Filter.eventually_cofinite.1 (hR.ae g)).union S.finite_toSet).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hc
    exact hv ((hS v hc.2 _).1 (hKA v _ hc.1))
  obtain ⟨W, hW⟩ : ∃ W : Set G, W = {g | ∀ v ∉ S, ∃ t, ∃ y ∈ K v, p v g = jv v t * y} := ⟨_, rfl⟩
  have hmem : ∀ g, g ∈ W ↔ ∀ v ∉ S, ∃ t, ∃ y ∈ K v, p v g = jv v t * y := by
    intro g; rw [hW]; rfl
  have hoff : ∀ g, g ∉ W → ∏ᶠ v, Fv v (p v g) = 0 := by
    intro g hg
    rw [hmem] at hg
    push_neg at hg
    obtain ⟨v, hv, hx⟩ := hg
    refine finprod_eq_zero _ v ((hS v hv _).2 ?_) (hfin g)
    rintro ⟨t, y, hy, e⟩
    exact hx t y hy e
  have hon : ∀ g ∈ W, ∏ᶠ v, Fv v (p v g) = ∏ v ∈ S, Fv v (p v g) := by
    intro g hg
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hc
    exact hv ((hS v hc _).1 ((hmem g).1 hg v hc))
  have hWopen : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' (US p K S : Set G), ?_,
      (continuous_const.mul continuous_id).isOpen_preimage _ (hR.opnU S), ?_⟩
    · intro x hx
      refine (hmem x).2 fun v hv => ?_
      obtain ⟨t, y, hy, e⟩ := (hmem g).1 hg v hv
      have hx' : p v (g⁻¹ * x) ∈ K v := hx v hv
      refine ⟨t, y * p v (g⁻¹ * x), mul_mem hy hx', ?_⟩
      rw [← mul_assoc, ← e, ← map_mul, mul_inv_cancel_left]
    · simp only [Set.mem_preimage, inv_mul_cancel]
      exact one_mem (US p K S)
  have hqm : Measurable q := hR.cq.measurable
  have hpm : ∀ v, Measurable (p v) := fun v => (hR.cp v).measurable
  have hmeas : Measurable fun g => Fi (q g) * ∏ v ∈ S, Fv v (p v g) :=
    (hFi.comp hqm).mul (Finset.measurable_prod _ fun v _ => (hFv v).1.comp (hpm v))
  have hEq : (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g)) =
      W.indicator (fun g => Fi (q g) * ∏ v ∈ S, Fv v (p v g)) := by
    funext g
    by_cases hg : g ∈ W
    · rw [Set.indicator_of_mem hg, hon g hg]
    · rw [Set.indicator_of_notMem hg, hoff g hg, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [hEq]
    exact hmeas.indicator hWopen.measurableSet
  · intro g h
    have hgW : g ∈ W := by
      by_contra hc
      exact h (by rw [hoff g hc, mul_zero])
    have hch : ∀ v, ∃ t : Tv v, (p v g ∈ K v → t = 1) ∧ (v ∉ S → (jv v t)⁻¹ * p v g ∈ K v) := by
      intro v
      by_cases hk : p v g ∈ K v
      · exact ⟨1, fun _ => rfl, fun _ => by simpa using hk⟩
      · by_cases hv : v ∈ S
        · exact ⟨1, fun h => absurd h hk, fun h => absurd hv h⟩
        · obtain ⟨t, y, hy, e⟩ := (hmem g).1 hgW v hv
          exact ⟨t, fun h => absurd h hk, fun _ => by rw [e]; simpa using hy⟩
    choose tv ht1 ht2 using hch
    obtain ⟨t, -, ht⟩ := hRT.surj 1 tv
      ((hR.ae g).mono fun v hv => by rw [ht1 v hv]; exact one_mem _)
    refine Set.mem_mul.2 ⟨j t, ⟨t, rfl⟩, (j t)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
    refine SetLike.mem_coe.2 (mem_US.2 fun v hv => ?_)
    rw [map_mul, map_inv, hp, ht]
    exact ht2 v hv
  · intro u hu
    have huW : u ∈ W := (hmem u).2 fun v hv => hKA v _ (hu v hv)
    rw [hon u huW, Finset.prod_coe_sort S (fun v => Fv v (p v u))]
