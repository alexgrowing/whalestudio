import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
open UpperTheory.V.Z.J.D
open scoped TensorProduct

namespace UpperTheory.V.Z.J.D

private lemma box_tmul {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (a : G) (b : H) (w : W) (v : W') :
    box ρ τ (a, b) (w ⊗ₜ[ℂ] v) = ρ a w ⊗ₜ[ℂ] τ b v := by
  simp [box, Representation.tprod_apply]

private lemma isot_factor {G H W W' X Y : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [Nontrivial W] (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (κ : Representation ℂ (G × H) X) (κ' : Representation ℂ H Y) (f : W ⊗[ℂ] Y ≃ₗ[ℂ] X)
    (hf : Intw (box ρ κ') κ f.toLinearMap) (h2 : Isot (κ.comp (MonoidHom.inr G H)) τ) :
    Isot κ' τ := by
  obtain ⟨w0, hw0⟩ := exists_ne (0 : W)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff ℂ w0).1 hcon)
  let p : X →ₗ[ℂ] Y := (TensorProduct.lid ℂ Y).toLinearMap ∘ₗ
    (TensorProduct.map φ LinearMap.id) ∘ₗ f.symm.toLinearMap
  have hp1 : ∀ w y, p (f (w ⊗ₜ[ℂ] y)) = φ w • y := fun w y => by
    simp [p]
  have hp2 : ∀ (h : H) (x : X), p (κ (1, h) x) = κ' h (p x) := by
    intro h x
    obtain ⟨t, rfl⟩ := f.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul w y =>
      have := hf (1, h) (w ⊗ₜ[ℂ] y)
      simp only [LinearEquiv.coe_coe] at this
      rw [← this, box_tmul, hp1, hp1]
      simp
  unfold Isot
  set S : Submodule ℂ Y := ⨆ g : {g : W' →ₗ[ℂ] Y // Intw τ κ' g}, LinearMap.range g.1 with hS
  have hle : (⊤ : Submodule ℂ X) ≤ S.comap p := by
    refine le_trans h2 (iSup_le fun u => ?_)
    rintro _ ⟨a, rfl⟩
    have hu : Intw τ κ' (p ∘ₗ u.1) := fun h v => by
      have := u.2 h v
      simp only [LinearMap.comp_apply]
      rw [this]
      exact hp2 h (u.1 v)
    exact (le_iSup (fun g : {g : W' →ₗ[ℂ] Y // Intw τ κ' g} => LinearMap.range g.1) ⟨_, hu⟩)
      ⟨a, rfl⟩
  intro y _
  have hy : p (f (w0 ⊗ₜ[ℂ] ((φ w0)⁻¹ • y))) ∈ S := hle (Submodule.mem_top)
  rw [hp1, smul_smul, mul_inv_cancel₀ hφ, one_smul] at hy
  exact hy

private lemma isot_tensor {G H W W' X Y : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G W) (τ : Representation ℂ H W')
    (κ : Representation ℂ (G × H) X) (κ' : Representation ℂ H Y) (f : W ⊗[ℂ] Y ≃ₗ[ℂ] X)
    (hf : Intw (box ρ κ') κ f.toLinearMap) (h : Isot κ' τ) : Isot κ (box ρ τ) := by
  unfold Isot
  set T : Submodule ℂ X :=
    ⨆ F : {F : W ⊗[ℂ] W' →ₗ[ℂ] X // Intw (box ρ τ) κ F}, LinearMap.range F.1 with hT
  have hF : ∀ g : W' →ₗ[ℂ] Y, Intw τ κ' g →
      Intw (box ρ τ) κ (f.toLinearMap ∘ₗ TensorProduct.map LinearMap.id g) := by
    intro g hg ab t
    obtain ⟨a, b⟩ := ab
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul w v =>
      have := hf (a, b) (w ⊗ₜ[ℂ] g v)
      simp only [LinearEquiv.coe_coe] at this
      rw [box_tmul] at this
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearEquiv.coe_coe, box_tmul]
      rw [hg b v, this]
  have hw : ∀ (w : W) (y : Y), f (w ⊗ₜ[ℂ] y) ∈ T := by
    intro w y
    have hle : (⊤ : Submodule ℂ Y) ≤
        T.comap (f.toLinearMap ∘ₗ TensorProduct.mk ℂ W Y w) := by
      refine le_trans h (iSup_le fun g => ?_)
      rintro _ ⟨a, rfl⟩
      exact (le_iSup (fun F : {F : W ⊗[ℂ] W' →ₗ[ℂ] X // Intw (box ρ τ) κ F} =>
        LinearMap.range F.1) ⟨_, hF g.1 g.2⟩) ⟨w ⊗ₜ[ℂ] a, by simp⟩
    exact hle (Submodule.mem_top (x := y))
  intro x _
  obtain ⟨t, rfl⟩ := f.surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht =>
    rw [map_add]
    exact T.add_mem (hs (Submodule.mem_top)) (ht (Submodule.mem_top))
  | tmul w y => exact hw w y

end UpperTheory.V.Z.J.D

theorem UpperTheory.V.Z.J.D.boxIsot :
    Step → BoxIsot := by
  intro hStep G H W W' _ _ _ _ _ _ ρ τ hρ _ X _ _ κ h1 h2
  obtain ⟨Y, _, _, κ', f, hf⟩ := hStep G H X W κ ρ hρ h1
  haveI : Nontrivial W := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    obtain ⟨s, t, hst⟩ := hρ.1.toNontrivial.exists_pair_ne
    exact hst (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  exact isot_tensor ρ τ κ κ' f hf (isot_factor ρ τ κ κ' f hf h2)
