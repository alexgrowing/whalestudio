import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI

open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.Poul

variable {G : Type} [Group G] {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {σ : G →* (H →L[ℂ] H)} {σ' : G →* (H' →L[ℂ] H')}

omit [CompleteSpace H] in
theorem inner_map_left (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) (v w : H) : ⟪σ g v, w⟫_ℂ = ⟪v, σ g⁻¹ w⟫_ℂ := by
  have h := (⟨(σ g : H →ₗ[ℂ] H), hiso g⟩ : H →ₗᵢ[ℂ] H).inner_map_map v (σ g⁻¹ w)
  have e : σ g (σ g⁻¹ w) = w := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  rw [← h]
  show _ = ⟪σ g v, σ g (σ g⁻¹ w)⟫_ℂ
  rw [e]

theorem exists_graph (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hiso' : ∀ g v, ‖σ' g v‖ = ‖v‖)
    (hs : ∀ T : H' →L[ℂ] H', (∀ g v, T (σ' g v) = σ' g (T v)) → ∃ c : ℂ, ∀ v, T v = c • v)
    (Γ : Submodule ℂ (H' × H)) (hcl : IsClosed (Γ : Set (H' × H))) (hinv : ∀ g, ∀ p ∈ Γ, (σ' g p.1, σ g p.2) ∈ Γ)
    {y₀ : H'} {z₀ : H} (h₀ : (y₀, z₀) ∈ Γ) (hy₀ : y₀ ≠ 0) :
    ∃ T : H' →L[ℂ] H, (∀ g y, T (σ' g y) = σ g (T y)) ∧ ∀ y, (y, T y) ∈ Γ := by
  let e : WithLp 2 (H' × H) ≃L[ℂ] H' × H := WithLp.prodContinuousLinearEquiv 2 ℂ H' H
  let V : Submodule ℂ (WithLp 2 (H' × H)) := Γ.comap (e : WithLp 2 (H' × H) →ₗ[ℂ] H' × H)
  have hV : IsClosed (V : Set (WithLp 2 (H' × H))) := hcl.preimage e.continuous
  have : CompleteSpace V := hV.completeSpace_coe
  let U : G → H' × H → WithLp 2 (H' × H) := fun g p => e.symm (σ' g p.1, σ g p.2)
  have hQ : ∀ g (p : H' × H), V.starProjection (U g p) = U g (e (V.starProjection (e.symm p))) := by
    intro g p
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
    · exact hinv g _ (V.starProjection_apply_mem (e.symm p))
    · have h1 := V.starProjection_inner_eq_zero (e.symm p) (U g⁻¹ (e w)) (hinv g⁻¹ _ hw)
      rw [← h1, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
      show ⟪σ' g p.1 - σ' g _, _⟫_ℂ + ⟪σ g p.2 - σ g _, _⟫_ℂ = _
      rw [← map_sub, ← map_sub, inner_map_left hiso', inner_map_left hiso]
      rfl
  let Q : H' →L[ℂ] H' × H :=
    (e : WithLp 2 (H' × H) →L[ℂ] H' × H) ∘L V.starProjection ∘L (e.symm : H' × H →L[ℂ] WithLp 2 (H' × H)) ∘L
      ContinuousLinearMap.inl ℂ H' H
  have hQa : ∀ y, Q y = e (V.starProjection (e.symm (y, 0))) := fun y => rfl
  have hQg : ∀ g y, Q (σ' g y) = (σ' g (Q y).1, σ g (Q y).2) := by
    intro g y
    have := hQ g (y, 0)
    simp only [U, map_zero] at this
    rw [hQa, this]
    rfl
  have hQm : ∀ y, Q y ∈ Γ := fun y => V.starProjection_apply_mem _
  obtain ⟨c, hc⟩ := hs (ContinuousLinearMap.fst ℂ H' H ∘L Q) fun g v => congrArg Prod.fst (hQg g v)
  have hc' : ∀ y, (Q y).1 = c • y := hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    set q := V.starProjection (e.symm (y₀, 0)) with hq
    have h1 := V.starProjection_inner_eq_zero (e.symm (y₀, 0)) q (V.starProjection_apply_mem _)
    have h2 := V.starProjection_inner_eq_zero (e.symm (y₀, 0)) (e.symm (y₀, z₀)) h₀
    rw [← hq, inner_sub_left] at h1 h2
    have h3 : ⟪e.symm (y₀, 0), q⟫_ℂ = 0 := by
      rw [WithLp.prod_inner_apply]
      show ⟪y₀, (Q y₀).1⟫_ℂ + ⟪(0 : H), _⟫_ℂ = 0
      rw [hc']; simp
    rw [h3, zero_sub, neg_eq_zero, inner_self_eq_zero] at h1
    rw [h1, inner_zero_left, sub_zero, WithLp.prod_inner_apply] at h2
    have h4 : ⟪y₀, y₀⟫_ℂ + ⟪(0 : H), z₀⟫_ℂ = 0 := h2
    rw [inner_zero_left, add_zero, inner_self_eq_zero] at h4
    exact hy₀ h4
  refine ⟨c⁻¹ • (ContinuousLinearMap.snd ℂ H' H ∘L Q), fun g y => ?_, fun y => ?_⟩
  · show c⁻¹ • (Q (σ' g y)).2 = σ g (c⁻¹ • (Q y).2)
    rw [hQg, map_smul]
  · have := Γ.smul_mem c⁻¹ (hQm y)
    convert this using 1
    refine Prod.ext ?_ rfl
    show y = c⁻¹ • (Q y).1
    rw [hc', smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem exists_op_of_form (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hiso' : ∀ g v, ‖σ' g v‖ = ‖v‖)
    (hs : ∀ T : H' →L[ℂ] H', (∀ g v, T (σ' g v) = σ' g (T v)) → ∃ c : ℂ, ∀ v, T v = c • v)
    (S : Set H) (S' : Set H') (hS : ∀ g, ∀ x ∈ S, σ g x ∈ S) (hS' : ∀ g, ∀ y ∈ S', σ' g y ∈ S') (B : H → H' → ℂ)
    (hB : ∀ g, ∀ x ∈ S, ∀ y ∈ S', B (σ g x) (σ' g y) = B x y) {y₀ : H'} {z₀ : H} (hy₀S : y₀ ∈ S') (hy₀ : y₀ ≠ 0)
    (h₀ : ∀ x ∈ S, B x y₀ = ⟪z₀, x⟫_ℂ) :
    ∃ T : H' →L[ℂ] H, (∀ g y, T (σ' g y) = σ g (T y)) ∧
      ∀ x ∈ S, ∀ w, (∀ y ∈ S', B x y = ⟪y, w⟫_ℂ) → ∀ y ∈ S', B x y = ⟪T y, x⟫_ℂ := by
  let Γ : Submodule ℂ (H' × H) :=
    { carrier := {p | ∀ x ∈ S, ∀ w, (∀ y ∈ S', B x y = ⟪y, w⟫_ℂ) → ⟪p.2, x⟫_ℂ = ⟪p.1, w⟫_ℂ}
      add_mem' := fun {p q} hp hq x hx w hw => by
        simp only [Prod.snd_add, Prod.fst_add, inner_add_left, hp x hx w hw, hq x hx w hw]
      zero_mem' := fun x _ w _ => by simp
      smul_mem' := fun c p hp x hx w hw => by
        simp only [Prod.smul_snd, Prod.smul_fst, inner_smul_left, hp x hx w hw] }
  have hcl : IsClosed (Γ : Set (H' × H)) := by
    have : (Γ : Set (H' × H)) = ⋂ x ∈ S, ⋂ w, ⋂ _ : (∀ y ∈ S', B x y = ⟪y, w⟫_ℂ),
        {p : H' × H | ⟪p.2, x⟫_ℂ = ⟪p.1, w⟫_ℂ} := by
      ext p; simp [Γ]
    rw [this]
    exact isClosed_biInter fun x _ => isClosed_iInter fun w => isClosed_iInter fun _ =>
      isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  have hinv : ∀ g, ∀ p ∈ Γ, (σ' g p.1, σ g p.2) ∈ Γ := by
    intro g p hp x hx w hw
    show ⟪σ g p.2, x⟫_ℂ = ⟪σ' g p.1, w⟫_ℂ
    rw [inner_map_left hiso, inner_map_left hiso']
    refine hp _ (hS _ x hx) _ fun y hy => ?_
    rw [← hB g _ (hS _ x hx) y hy, ← inner_map_left hiso', ← hw _ (hS' g y hy), ← ContinuousLinearMap.mul_apply,
      ← map_mul, mul_inv_cancel, map_one]
    rfl
  obtain ⟨T, hT, hΓ⟩ := exists_graph hiso hiso' hs Γ hcl hinv (y₀ := y₀) (z₀ := z₀)
    (fun x hx w hw => (h₀ x hx).symm.trans (hw y₀ hy₀S)) hy₀
  exact ⟨T, hT, fun x hx w hw y hy => (hw y hy).trans (hΓ y x hx w hw).symm⟩

end CompanionTheory.D.gk.Poul
