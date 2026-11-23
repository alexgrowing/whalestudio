import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RigidOrth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.DiagSubIsKIrrHW

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rigid_universal {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} (hσ₁ : IsURepOn (UJset ε) σ₁)
    {D₁ : Submodule ℂ H₁} {E₁ : Fin n → Fin n → Module.End ℂ D₁} (hD₁ : IsDerivedOn ε σ₁ D₁ E₁)
    {V₁ : Submodule ℂ D₁} (hV₁ : IsKIrrHW ε E₁ (lowK ε lam) V₁)
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = (casVal lam : ℂ) • v)
    (hVK₁ : ∀ k ∈ Kset ε, ∀ v ∈ V₁, ∃ w ∈ V₁, (w : H₁) = σ₁ k v)
    {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} (hσ₂ : IsURepOn (UJset ε) σ₂)
    {D₂ : Submodule ℂ H₂} {E₂ : Fin n → Fin n → Module.End ℂ D₂} (hD₂ : IsDerivedOn ε σ₂ D₂ E₂)
    {V₂ : Submodule ℂ D₂} (hV₂ : IsKIrrHW ε E₂ (lowK ε lam) V₂)
    (hc₂ : ∀ v ∈ V₂, casimir E₂ v = (casVal lam : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : H₂) = σ₂ k v)
    (hgap : StdGap ε lam) (φ : V₁ →ₗ[ℂ] V₂)
    (hφK : ∀ k ∈ Kset ε, ∀ (v : V₁) (w : V₁), ((w : D₁) : H₁) = σ₁ k ((v : D₁) : H₁) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂))
    (hφI : ∀ v v' : V₁, inner ℂ (((φ v' : V₂) : D₂) : H₂) (((φ v : V₂) : D₂) : H₂) =
      inner ℂ ((v' : D₁) : H₁) ((v : D₁) : H₁)) :
    ∀ g ∈ UJset ε, ∀ v v' : V₁,
      inner ℂ (((φ v' : V₂) : D₂) : H₂) (σ₂ g (((φ v : V₂) : D₂) : H₂)) =
        inner ℂ ((v' : D₁) : H₁) (σ₁ g ((v : D₁) : H₁)) := by
  have : FiniteDimensional ℂ V₁ := hV₁.1
  have hσ := USum.isURepOn_sσ hσ₁ hσ₂
  have hD := USum.isDerivedOn_sσ hD₁ hD₂
  have hcomm := fun a b (hab : ε a = ε b) (v : V₁) =>
    USum.phi_E_comm hD₁ hD₂ hV₁.2.1 hVK₁ φ hφK hab v
  have hV := USum.diagSub_isKIrrHW φ hV₁ hcomm
  have hc := USum.casimir_diagSub (E₁ := E₁) (E₂ := E₂) φ hc₁ hc₂
  have hVK : ∀ k ∈ Kset ε, ∀ x ∈ USum.diagSub φ, ∃ w ∈ USum.diagSub φ,
      (w : WithLp 2 (H₁ × H₂)) = USum.sσ σ₁ σ₂ k x := by
    rintro k hk _ ⟨v, rfl⟩
    obtain ⟨w₁, hw₁, e⟩ := hVK₁ k hk _ v.2
    refine ⟨USum.diagι φ ⟨w₁, hw₁⟩, ⟨_, rfl⟩, ?_⟩
    rw [USum.coe_diagι, USum.coe_diagι]
    show _ = WithLp.toLp 2 (σ₁ k ((v : D₁) : H₁), σ₂ k (((φ v : V₂) : D₂) : H₂))
    rw [← e, ← hφK k hk v ⟨w₁, hw₁⟩ e]
  let R : WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) := USum.sop 1 (-1)
  let j' : USum.diagSub φ →ₗ[ℂ] WithLp 2 (H₁ × H₂) :=
    R.toLinearMap ∘ₗ (USum.sD D₁ D₂).subtype ∘ₗ (USum.diagSub φ).subtype
  have hj : ∀ k ∈ Kset ε, ∀ v w : USum.diagSub φ,
      (((w : USum.sD D₁ D₂)) : WithLp 2 (H₁ × H₂)) = USum.sσ σ₁ σ₂ k ((v : USum.sD D₁ D₂) : _) →
      j' w = USum.sσ σ₁ σ₂ k (j' v) := by
    intro k _ v w h
    show USum.sop 1 (-1) ((w : USum.sD D₁ D₂) : WithLp 2 (H₁ × H₂)) =
      USum.sop (σ₁ k) (σ₂ k) (USum.sop 1 (-1) ((v : USum.sD D₁ D₂) : WithLp 2 (H₁ × H₂)))
    rw [h]
    exact USum.sop_neg_comm _ _ _
  have horth : ∀ v v' : USum.diagSub φ, inner ℂ (j' v') ((v : USum.sD D₁ D₂) : WithLp 2 (H₁ × H₂)) = 0 := by
    rintro ⟨_, ⟨v, rfl⟩⟩ ⟨_, ⟨v', rfl⟩⟩
    show inner ℂ (WithLp.toLp 2 (((v' : D₁) : H₁), -(((φ v' : V₂) : D₂) : H₂)))
      (WithLp.toLp 2 (((v : D₁) : H₁), (((φ v : V₂) : D₂) : H₂))) = 0
    rw [USum.inner_sum]
    simp only [inner_neg_left, hφI]
    exact add_neg_cancel _
  intro g hg v v'
  have key := rigid_orth hgap hσ hD hV hc hVK j' hj horth g hg
    ⟨USum.diagι φ v, ⟨v, rfl⟩⟩ ⟨USum.diagι φ v', ⟨v', rfl⟩⟩
  change inner ℂ (WithLp.toLp 2 (((v' : D₁) : H₁), -(((φ v' : V₂) : D₂) : H₂)))
    (USum.sop (σ₁ g) (σ₂ g) (WithLp.toLp 2 (((v : D₁) : H₁), (((φ v : V₂) : D₂) : H₂)))) = 0 at key
  rw [USum.inner_sum, USum.sop_apply] at key
  simp only [inner_neg_left] at key
  rw [← sub_eq_add_neg, sub_eq_zero] at key
  exact key.symm

end ReciprocityTheory.ChartRestriction.DS
