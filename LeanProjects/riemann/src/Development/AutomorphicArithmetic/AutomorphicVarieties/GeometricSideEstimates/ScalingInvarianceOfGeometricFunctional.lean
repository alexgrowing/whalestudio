import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideEstimate

open UpperTheory.V.Lit.Geo

private theorem scale_mono {ι : Type} {q : ι → ℝ} {N M : ℕ} (h : Scale q N) (hNM : N ≤ M) : Scale q M := by
  refine ⟨h.1, fun s t hs hst => ⟨(h.2 s t hs hst).1, (h.2 s t hs hst).2.trans ?_⟩⟩
  refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ((one_le_div hs).2 hst) hNM) ?_
  exact tsum_nonneg fun i => (Real.exp_pos _).le

private theorem scale_equiv {ι κ : Type} (e : ι ≃ κ) {q : κ → ℝ} {N : ℕ} (h : Scale q N) :
    Scale (fun i => q (e i)) N := by
  refine ⟨fun i => h.1 _, fun s t hs hst => ⟨?_, ?_⟩⟩
  · exact (e.summable_iff (f := fun k => Real.exp (-Real.pi * (s * q k)))).2 (h.2 s t hs hst).1
  · rw [e.tsum_eq (fun k => Real.exp (-Real.pi * (s * q k))), e.tsum_eq (fun k => Real.exp (-Real.pi * (t * q k)))]
    exact (h.2 s t hs hst).2

theorem UpperTheory.scaling_invariance_of_geometric_functional :
    ScaleGen := by
  intro A V _ _ _ _ φ ε hε hφ
  let W : Submodule ℝ V := Submodule.span ℝ (Set.range φ)
  let L : Submodule ℤ W := (φ.range.comap W.subtype.toAddMonoidHom).toIntSubmodule
  have hmem : ∀ w : W, w ∈ L ↔ (w : V) ∈ Set.range φ := fun w => Iff.rfl
  have hnorm : ∀ y : L, y ≠ 0 → ε ≤ ‖y‖ := by
    intro y hy
    obtain ⟨a, ha⟩ := (hmem y).1 y.2
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hy
      apply Subtype.ext
      apply Subtype.ext
      simpa using ha.symm
    have := hφ a ha0
    rw [ha] at this
    exact this
  haveI : DiscreteTopology L := by
    apply discreteTopology_of_isOpen_singleton_zero
    rw [Metric.isOpen_singleton_iff]
    refine ⟨ε, hε, fun y hy => ?_⟩
    by_contra hne
    rw [dist_zero_right] at hy
    linarith [hnorm y hne]
  haveI : IsZLattice ℝ L := by
    refine ⟨?_⟩
    have hs : (L : Set W) = ((↑) : W → V) ⁻¹' Set.range φ := rfl
    rw [hs]
    exact Submodule.span_span_coe_preimage
  have hinj : Function.Injective φ := by
    intro a b hab
    by_contra hne
    have h0 := hφ (a - b) (sub_ne_zero.mpr hne)
    rw [map_sub, hab, sub_self, norm_zero] at h0
    linarith
  let e : A ≃ L := Equiv.ofBijective
    (fun a => ⟨⟨φ a, Submodule.subset_span ⟨a, rfl⟩⟩, ⟨a, rfl⟩⟩)
    ⟨fun a b hab => hinj (congrArg (fun y : L => ((y : W) : V)) hab), fun y => by
      obtain ⟨a, ha⟩ := (hmem y).1 y.2
      exact ⟨a, Subtype.ext (Subtype.ext ha)⟩⟩
  have hL := UpperTheory.geometric_side_estimate W L
  have h1 := scale_equiv e hL
  exact scale_mono h1 (Submodule.finrank_le W)
