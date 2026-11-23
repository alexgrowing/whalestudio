import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.EmbComb

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section

namespace ChA

lemma finite_sep {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Set V) (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) (R : ℝ) :
    {x | x ∈ S ∧ ‖x‖ ≤ R}.Finite := by
  classical
  have hcpt : IsCompact (Metric.closedBall (0 : V) R) := isCompact_closedBall 0 R
  obtain ⟨t, htfin, hcov⟩ :=
    (Metric.totallyBounded_iff.mp hcpt.totallyBounded) (1 / 2) (by norm_num)
  have hT : ∀ x ∈ {x | x ∈ S ∧ ‖x‖ ≤ R}, ∃ y ∈ t, dist x y < 1 / 2 := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : V) R := by
      rw [mem_closedBall_zero_iff]; exact hx.2
    have := hcov hx'
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at this
    exact this
  choose! f hf hfx using hT
  refine Set.Finite.of_finite_image (f := f) (htfin.subset ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hf x hx
  · intro x hx y hy hxy
    by_contra hne
    have hsep := hS x hx.1 y hy.1 hne
    have h1 := hfx x hx
    have h2 := hfx y hy
    rw [hxy] at h1
    have hlt : dist x y < 1 := by
      calc dist x y ≤ dist x (f y) + dist y (f y) := dist_triangle_right _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
        _ = 1 := by norm_num
    rw [dist_eq_norm] at hlt
    linarith

lemma sep_of_group {V : Type} [NormedAddCommGroup V] (G : AddSubgroup V)
    (hG : ∀ g ∈ G, g ≠ 0 → 1 ≤ ‖g‖) (S : Set V) (hS : S ⊆ G) :
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖ := by
  intro x hx y hy hne
  exact hG (x - y) (G.sub_mem (hS hx) (hS hy)) (sub_ne_zero.mpr hne)

lemma exists_closest {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (G : AddSubgroup V) (hG : ∀ g ∈ G, g ≠ 0 → 1 ≤ ‖g‖) (p : V) :
    ∃ w ∈ G, ∀ w' ∈ G, ‖p - w‖ ≤ ‖p - w'‖ := by
  classical
  have hsep := sep_of_group G hG (G : Set V) subset_rfl
  have hfin : {x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖}.Finite := finite_sep _ hsep _
  have hne : ({x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖} : Set V).Nonempty :=
    ⟨0, G.zero_mem, by simp⟩
  obtain ⟨w, hw, hmin⟩ := Set.exists_min_image _ (fun w => ‖p - w‖) hfin hne
  refine ⟨w, hw.1, fun w' hw' => ?_⟩
  by_cases h : ‖w'‖ ≤ 2 * ‖p‖
  · exact hmin w' ⟨hw', h⟩
  · push Not at h
    have h0 := hmin 0 ⟨G.zero_mem, by simp⟩
    simp only [sub_zero] at h0
    have h3 : ‖w'‖ - ‖p‖ ≤ ‖p - w'‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le w' p
    linarith

lemma cover (hNP : Ext.NearestPlane) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (G : Set V) (ℓ : ℝ) (hG : ∀ g ∈ G, ‖g‖ ≤ ℓ) (D : ℕ)
    (hD : Module.finrank ℝ (Submodule.span ℝ G) ≤ D) {z : V} (hz : z ∈ Submodule.span ℝ G) :
    ∃ g ∈ AddSubgroup.closure G, ‖z - g‖ ^ 2 ≤ D * ℓ ^ 2 / 4 := by
  classical
  obtain ⟨b, hbG, hbspan, hbli⟩ := exists_linearIndependent ℝ G
  have hbfin : b.Finite := LinearIndependent.setFinite hbli
  let _ : Fintype b := hbfin.fintype
  let e := Fintype.equivFin b
  let v : Fin (Fintype.card b) → V := fun i => (e.symm i : V)
  have hv : LinearIndependent ℝ v := hbli.comp _ e.symm.injective
  have hvG : ∀ i, v i ∈ G := fun i => hbG (e.symm i).2
  have hrange : Set.range v = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [v]⟩
  have hn : Fintype.card b ≤ D := by
    have h := finrank_span_set_eq_card (R := ℝ) hbli
    rw [hbspan, Set.toFinset_card] at h
    omega
  have hz' : z ∈ Submodule.span ℝ (Set.range v) := by
    rw [hrange, hbspan]; exact hz
  obtain ⟨c, hc⟩ := hNP V (Fintype.card b) v hv z hz'
  refine ⟨∑ i, (c i : ℝ) • v i, ?_, ?_⟩
  · refine AddSubgroup.sum_mem _ (fun i _ => ?_)
    rw [Int.cast_smul_eq_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (hvG i)) _
  · have hsum : ∑ i, ‖v i‖ ^ 2 ≤ (Fintype.card b : ℝ) * ℓ ^ 2 := by
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin (Fintype.card b), ℓ ^ 2 :=
            Finset.sum_le_sum (fun i _ => by
              have h1 := hG (v i) (hvG i)
              gcongr)
        _ = (Fintype.card b : ℝ) * ℓ ^ 2 := by simp
    have hnD : (Fintype.card b : ℝ) ≤ D := by exact_mod_cast hn
    have hl : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
    nlinarith

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
