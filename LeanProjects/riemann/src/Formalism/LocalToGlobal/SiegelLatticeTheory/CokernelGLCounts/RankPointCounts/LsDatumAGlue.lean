import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACut

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section GlueDefs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def Corr (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') (n₁ n₂ : V) : Prop :=
  ∃ (h₁ : n₁ ∈ H.W0 t₁.f t₁.f') (h₂ : n₂ ∈ H.W0 t₂.f t₂.f'),
    φ (H.mkW t₁.f ⟨n₁, mem_perp_isotropicSpan_of_mem_framePerp H h₁⟩) = H.mkW t₂.f ⟨n₂, mem_perp_isotropicSpan_of_mem_framePerp H h₂⟩ ∧
    φ' (H.mkW t₁.f' ⟨n₁, mem_perp_isotropicSpan_of_mem_framePerp' H h₁⟩) = H.mkW t₂.f' ⟨n₂, mem_perp_isotropicSpan_of_mem_framePerp' H h₂⟩

def ThCond (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Prop :=
  ∀ n₁ n₂, Corr H t₁ t₂ φ φ' n₁ n₂ → (n₁ ∈ t₁.abelian₂ ↔ n₂ ∈ Λ₂)

def GlueRel (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (m₁ : ↥(MMsharp H t₁)) (m₂ : ↥(MMsharp H t₂)) : Prop :=
  ∃ n₁ n₂, Corr H t₁ t₂ φ φ' n₁ n₂ ∧ (m₁ : V) + n₁ ∈ t₁.abelian₂ ∧ (m₂ : V) + n₂ ∈ Λ₂

def GamCond (H : HermSp M V) {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) : Prop :=
  (M.split = none →
      (fun p => (θ p.1, φ p.2)) '' Gam H t₁ = Gam H t₂ ∧ (fun p => (θ p.1, φ' p.2)) '' Gam' H t₁ = Gam' H t₂) ∧
    (∀ g : SplitG M.L, M.split = some g →
      (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
        GamR H t₂ (algebraMap F E (g.q : F)))

end GlueDefs

section GlueProps

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def Glue (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∃ e : {Λ₂ : Submodule M.L.O V // H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
        ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ'} ≃
      {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ //
        IsUnit (H.Dl f₂ f₂' (r + 1)) ∧ MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ ∧ IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ},
      ∀ x m₁ m₂, (e x).1 (ddMk H t₁ m₁) = ddMk H _ m₂ ↔
        GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ x.1 φ φ' m₁ m₂

def ClaimR (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' →
    ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩,
      (∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂) →
      (H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' ↔
        GamCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' θ)

theorem latSide_of (M : Model F E) (r n : ℕ) (hG : Glue M r n) (hR : ClaimR M r n) : LatSide M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp
  obtain ⟨e, he⟩ := hG V H hn t₁ f₂ f₂' φ φ' hyp
  have hR' := hR V H hn t₁ f₂ f₂' φ φ' hyp
  have thc : ∀ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' → ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' := by
    intro Λ₂ hg hr n₁ n₂ hc
    obtain ⟨h₁, h₂, c₁, c₂⟩ := hc
    exact thCorr_holds M r V H t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' hyp.1 hg hr n₁ h₁ n₂ h₂ c₁ c₂
  have heq : ∀ y, ∀ m₁ m₂, y.1 (ddMk H t₁ m₁) = ddMk H _ m₂ ↔
      GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ (e.symm y).1 φ φ' m₁ m₂ := by
    intro y m₁ m₂
    have := he (e.symm y) m₁ m₂
    rwa [e.apply_symm_apply] at this
  refine Nat.card_congr
    { toFun := fun Λ => ⟨(e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).1,
        (e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).2.1, (e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).2.2.1,
        (e ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩).2.2.2,
        ((hR' Λ.1 Λ.2.1 (thc Λ.1 Λ.2.1 Λ.2.2) _ (he ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩)).1 Λ.2.2).1,
        ((hR' Λ.1 Λ.2.1 (thc Λ.1 Λ.2.1 Λ.2.2) _ (he ⟨Λ.1, Λ.2.1, thc Λ.1 Λ.2.1 Λ.2.2⟩)).1 Λ.2.2).2⟩
      invFun := fun θ => ⟨(e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).1, (e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).2.1,
        (hR' _ (e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).2.1 (e.symm ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩).2.2 θ.1
          (heq ⟨θ.1, θ.2.1, θ.2.2.1, θ.2.2.2.1⟩)).2 θ.2.2.2.2⟩
      left_inv := fun Λ => by
        apply Subtype.ext
        simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
      right_inv := fun θ => by
        apply Subtype.ext
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply] }

end GlueProps

end Formalism.L2.SG.LsDatumA
