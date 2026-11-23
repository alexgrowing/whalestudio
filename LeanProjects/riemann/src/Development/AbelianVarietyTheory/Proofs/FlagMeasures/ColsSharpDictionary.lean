import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St

section Abstract

open Formalism.L2.SG.ColsDim

theorem cols_sharp_abstract {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (ιi : Γ →* Gi) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (ψ : K →* ℂˣ) (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ)
    (hψ : ∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1)
    (sh : (V →ₗ[ℂ] (Gi × Gf → ℂ)) → Gf → V)
    (hsh : ∀ (T : V →ₗ[ℂ] (Gi × Gf → ℂ)) (x : Gf) (ξ : V), ⟪sh T x, ξ⟫_ℂ = T ξ (1, x)) :
    (∀ (T : Cols ℂ ιi ιf K ψ π) (γ : Γ) (x : Gf) (κ : K),
      sh T.1 (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (sh T.1 x)) ∧
    (∀ T : Cols ℂ ιi ιf K ψ π, (∀ x, sh T.1 x = 0) → T = 0) ∧
    ∀ φ : Gf → V, (∀ (γ : Γ) (x : Gf) (κ : K),
      φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) →
      ∃ T : Cols ℂ ιi ιf K ψ π, ∀ x, sh T.1 x = φ x := by
  obtain ⟨e, he, hsm⟩ := sharp_bijective Γ Gi Gf V ιi ιf K ψ π hπ hψ
  have key : ∀ (T : Cols ℂ ιi ιf K ψ π) (x : Gf), sh T.1 x = (e T).1 x := fun T x =>
    ext_inner_right ℂ fun ξ => by
      rw [hsh]
      exact he T x ξ
  refine ⟨?_, ?_, ?_⟩
  · intro T γ x κ
    rw [key, key]
    exact (e T).2 γ x κ
  · intro T hT
    have h0 : e T = e ((0 : ℂ) • T) := by
      apply Subtype.ext
      rw [hsm]
      funext x
      rw [← key, hT x]
      simp
    have := e.injective h0
    rw [this]
    simp
  · intro φ hφ
    refine ⟨e.symm ⟨φ, hφ⟩, fun x => ?_⟩
    rw [key, Equiv.apply_symm_apply]

end Abstract

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cols_sharp_dictionary :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), (∀ κ : Ku X u hK, ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1) ∧ (∀ (h : Hinf X u) (v w : X.Vpi u), ⟪piRep X u h v, piRep X u h w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ (T : Cu X u hK) (γ : Gam X u) (x : Hfin X u) (κ : Ku X u hK), shP X u T.1 (iotaF X u γ * x * κ) = (((psiK X u hK κ)⁻¹ : ℂˣ) : ℂ) • piRep X u (iotaI X u γ) (shP X u T.1 x)) ∧ (∀ T : Cu X u hK, (∀ x, shP X u T.1 x = 0) → T = 0) ∧ ∀ φ : Hfin X u → X.Vpi u, (∀ (γ : Gam X u) (x : Hfin X u) (κ : Ku X u hK), φ (iotaF X u γ * x * κ) = (((psiK X u hK κ)⁻¹ : ℂˣ) : ℂ) • piRep X u (iotaI X u γ) (φ x)) → ∃ T : Cu X u hK, ∀ x, shP X u T.1 x = φ x := by
  intro D X u hK
  have hψ : ∀ κ : Ku X u hK, ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1 := fun κ => hK.2.2.2.2 _ κ.2
  have hπ : ∀ (h : Hinf X u) (v w : X.Vpi u), ⟪piRep X u h v, piRep X u h w⟫_ℂ = ⟪v, w⟫_ℂ :=
    fun h v w => (X.piU_rep u).2.2.1 _ (hinf_le_sinf X u _ h.2) v w
  exact ⟨hψ, hπ, cols_sharp_abstract (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) (piRep X u) hπ hψ
    (shP X u) (inner_shP X u)⟩

end GlobalTheory.St

end
