import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.traceLine :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V), Module.finrank ℂ W = 1 → ∀ (B : V →ₗ[ℂ] V) (m : ℂ), m ≠ 0 →
      (∀ v, B v ∈ W) → (∀ v ∈ W, B v = m • v) → ∀ A : V ≃ₗ[ℂ] V, (∀ v ∈ W, A v ∈ W) →
        ∃ c : ℂ, c ≠ 0 ∧ HasFinTrace (B ∘ₗ (A : V →ₗ[ℂ] V)) c := by
  intro V _ _ W hW B m hm hB hBW A hA
  have hR : LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V)) = W := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact hB _
    · intro w hw
      refine ⟨A.symm (m⁻¹ • w), ?_⟩
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [hBW _ (W.smul_mem _ hw), smul_smul, mul_inv_cancel₀ hm, one_smul]
  have h1 : Module.finrank ℂ (LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V))) = 1 := by rw [hR, hW]
  have hfin : FiniteDimensional ℂ (LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V))) :=
    Module.finite_of_finrank_eq_succ h1
  refine ⟨_, ?_, hfin, rfl⟩
  set f := (B ∘ₗ (A : V →ₗ[ℂ] V)).restrict (p := LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V)))
    (q := LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V)))
    (fun v _ => LinearMap.mem_range_self (B ∘ₗ (A : V →ₗ[ℂ] V)) v) with hf
  obtain ⟨v, hv, hgen⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c, hc⟩ := hgen (f v)
  have hfc : f = c • LinearMap.id := by
    ext1 w
    obtain ⟨a, rfl⟩ := hgen w
    rw [map_smul, ← hc, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h2 : ((f v : LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V))) : V) = 0 := by
      rw [← hc]; simp
    have h3 : B (A (v : V)) = 0 := h2
    have hvW : (v : V) ∈ W := hR ▸ v.2
    rw [hBW _ (hA _ hvW), smul_eq_zero] at h3
    rcases h3 with h3 | h3
    · exact hm h3
    · exact hv (Subtype.ext (by simpa using h3))
  rw [hfc, map_smul, LinearMap.trace_id, h1]
  simpa using hc0
