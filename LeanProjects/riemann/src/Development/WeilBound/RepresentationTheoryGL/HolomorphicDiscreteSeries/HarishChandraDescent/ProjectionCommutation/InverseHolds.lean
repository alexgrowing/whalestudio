import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent

noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

namespace InverseCommuting

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commute_proj (K : Submodule ℂ H) [K.HasOrthogonalProjection] (A : H →L[ℂ] H)
    (hA : ∀ x ∈ K, A x ∈ K) (hA' : ∀ x ∈ K, ContinuousLinearMap.adjoint A x ∈ K) :
    Commute K.starProjection A := by
  have hPmem : ∀ v : H, K.starProjection v ∈ K := by
    intro v
    rw [Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  have hzero : ∀ v ∈ Kᗮ, K.starProjection v = 0 := by
    intro v hv
    rw [Submodule.starProjection_apply, Submodule.coe_eq_zero]
    exact Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hv
  show K.starProjection * A = A * K.starProjection
  ext x
  simp only [ContinuousLinearMap.mul_apply]
  have hw : x - K.starProjection x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
  have hAw : A (x - K.starProjection x) ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact (Submodule.mem_orthogonal _ _).1 hw _ (hA' k hk)
  have e1 : K.starProjection (A (K.starProjection x)) = A (K.starProjection x) :=
    Submodule.starProjection_eq_self_iff.2 (hA _ (hPmem x))
  have e2 := hzero _ hAw
  have hx : x = K.starProjection x + (x - K.starProjection x) := by abel
  calc K.starProjection (A x)
      = K.starProjection (A (K.starProjection x)) + K.starProjection (A (x - K.starProjection x)) := by
        conv_lhs => rw [hx]
        rw [map_add, map_add]
    _ = A (K.starProjection x) := by rw [e1, e2, add_zero]

end InverseCommuting

open InverseCommuting

set_option maxHeartbeats 800000 in
theorem inverse_holds : Inv := by
  intro H _ _ _ D B ι U hD hB hnorm hadj hU hcomm
  let f : ↥D →ₗ[ℂ] H := D.subtype ∘ₗ B
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : ‖x - y‖ ≤ ‖B (x - y)‖ := hnorm _
    have h0 : B (x - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 (Subtype.ext hxy)
    rw [h0, norm_zero] at h1
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  let R : Submodule ℂ H := LinearMap.range f
  let eqv : ↥D ≃ₗ[ℂ] ↥R := LinearEquiv.ofInjective f hf_inj
  have heqv : ∀ z : ↥D, ((eqv z : ↥R) : H) = ((B z : ↥D) : H) := fun z => LinearEquiv.ofInjective_apply f z
  let g₀ : ↥R →ₗ[ℂ] H := D.subtype ∘ₗ eqv.symm.toLinearMap
  have hg₀ : ∀ r : ↥R, ‖g₀ r‖ ≤ 1 * ‖r‖ := by
    intro r
    have h2 := heqv (eqv.symm r)
    rw [eqv.apply_symm_apply] at h2
    rw [one_mul]
    calc ‖g₀ r‖ = ‖eqv.symm r‖ := rfl
      _ ≤ ‖B (eqv.symm r)‖ := hnorm _
      _ = ‖(r : H)‖ := by
        show ‖((B (eqv.symm r) : ↥D) : H)‖ = ‖(r : H)‖
        rw [h2]
      _ = ‖r‖ := rfl
  let g : ↥R →L[ℂ] H := g₀.mkContinuous 1 hg₀
  have hgB : ∀ x : ↥D, g ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩ = x := by
    intro x
    show ((eqv.symm ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩ : ↥D) : H) = x
    congr 1
    apply eqv.injective
    rw [eqv.apply_symm_apply]
    apply Subtype.ext
    exact (heqv x).symm
  have hUR : ∀ i, ∀ v ∈ R, U i v ∈ R := by
    rintro i v ⟨x, rfl⟩
    obtain ⟨y, -, hy2⟩ := hU i x
    exact ⟨y, hy2⟩
  let K : Submodule ℂ H := R.topologicalClosure
  have hKcl : IsClosed (K : Set H) := R.isClosed_topologicalClosure
  have hUK : ∀ i, ∀ v ∈ K, U i v ∈ K := by
    intro i
    have hle : R ≤ K.comap (U i : H →ₗ[ℂ] H) := fun v hv => R.le_topologicalClosure (hUR i v hv)
    have hcl : IsClosed ((K.comap (U i : H →ₗ[ℂ] H) : Set H)) := hKcl.preimage (U i).continuous
    intro v hv
    exact Submodule.topologicalClosure_minimal R hle hcl hv
  haveI : IsClosed (K : Set H) := hKcl
  haveI : CompleteSpace K := IsClosed.completeSpace_coe
  have hPcomm : ∀ i, Commute K.starProjection (U i) := by
    intro i
    refine commute_proj K (U i) (hUK i) ?_
    intro v hv
    obtain ⟨j, hj⟩ := hadj i
    rw [hj]
    exact hUK j v hv
  have hDK : ∀ x : ↥D, (x : H) ∈ K := by
    intro x
    obtain ⟨y, hy1, hy2⟩ := hcomm K.starProjection hPcomm x
    have hBx : K.starProjection ((B x : ↥D) : H) = ((B x : ↥D) : H) :=
      Submodule.starProjection_eq_self_iff.2 (R.le_topologicalClosure ⟨x, rfl⟩)
    have hByx : B y = B x := Subtype.ext (hy2.trans hBx)
    have hyx : y = x := hf_inj (by
      show ((B y : ↥D) : H) = ((B x : ↥D) : H)
      rw [hByx])
    apply Submodule.starProjection_eq_self_iff.1
    rw [← hy1, hyx]
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    have hsub : (D : Set H) ⊆ K := fun v hv => hDK ⟨v, hv⟩
    intro v _
    have hv : v ∈ closure (D : Set H) := by
      rw [hD.closure_eq]
      trivial
    exact (closure_minimal hsub hKcl) hv
  have hRd : Dense (R : Set H) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe]
    show ((K : Set H)) = Set.univ
    rw [hKtop]
    rfl
  have hRdense : DenseRange R.subtypeL := hRd.denseRange_val
  have hRui : IsUniformInducing R.subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
  let T : H →L[ℂ] H := g.extend R.subtypeL
  have hT : ∀ r : ↥R, T r = g r := fun r => ContinuousLinearMap.extend_eq g hRdense hRui r
  have hTB : ∀ x : ↥D, T ((B x : ↥D) : H) = x := by
    intro x
    have h3 := hT ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩
    rw [hgB] at h3
    exact h3
  have base : ∀ x y : ↥D, ⟪T ((B x : ↥D) : H), ((B y : ↥D) : H)⟫_ℂ = ⟪((B x : ↥D) : H), T ((B y : ↥D) : H)⟫_ℂ := by
    intro x y
    rw [hTB, hTB]
    exact (hB x y).symm
  have step1 : ∀ (u : H) (y : ↥D), ⟪T u, ((B y : ↥D) : H)⟫_ℂ = ⟪u, T ((B y : ↥D) : H)⟫_ℂ := by
    intro u y
    have hfun := Continuous.ext_on hRd (T.continuous.inner continuous_const)
      (continuous_id.inner continuous_const)
      (f := fun u => ⟪T u, ((B y : ↥D) : H)⟫_ℂ) (g := fun u => ⟪u, T ((B y : ↥D) : H)⟫_ℂ)
      (by
        rintro _ ⟨x, rfl⟩
        exact base x y)
    exact congrFun hfun u
  have hsym : ∀ u v : H, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ := by
    intro u v
    have hfun := Continuous.ext_on hRd (continuous_const.inner continuous_id)
      (continuous_const.inner T.continuous)
      (f := fun v => ⟪T u, v⟫_ℂ) (g := fun v => ⟪u, T v⟫_ℂ)
      (by
        rintro _ ⟨y, rfl⟩
        exact step1 u y)
    exact congrFun hfun v
  refine ⟨T, ?_, ?_, hTB⟩
  · show star T = T
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ((ContinuousLinearMap.eq_adjoint_iff T T).2 hsym).symm
  · intro i
    show T * U i = U i * T
    apply ContinuousLinearMap.coeFn_injective
    refine Continuous.ext_on hRd (T * U i).continuous (U i * T).continuous ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy1, hy2⟩ := hU i x
    show T (U i ((B x : ↥D) : H)) = U i (T ((B x : ↥D) : H))
    rw [← hy2, hTB, hTB, hy1]

end PositivityTheory.RgHe3
