import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.SopNegComm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.InKRealSmul

noncomputable section

open Finset Matrix WithLp

namespace ReciprocityTheory.ChartRestriction.DS

namespace USum

variable {n : ℕ} {ε : Fin n → Bool}
variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
  {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
  {V₁ : Submodule ℂ D₁} {V₂ : Submodule ℂ D₂}

def diagι (φ : V₁ →ₗ[ℂ] V₂) : V₁ →ₗ[ℂ] sD D₁ D₂ :=
  ofP ∘ₗ (V₁.subtype.prod (V₂.subtype ∘ₗ φ))

theorem diagι_apply (φ : V₁ →ₗ[ℂ] V₂) (v : V₁) :
    diagι φ v = ofP ((v : D₁), ((φ v : V₂) : D₂)) := rfl

theorem coe_diagι (φ : V₁ →ₗ[ℂ] V₂) (v : V₁) :
    ((diagι φ v : sD D₁ D₂) : WithLp 2 (H₁ × H₂)) =
      toLp 2 (((v : D₁) : H₁), (((φ v : V₂) : D₂) : H₂)) := rfl

def diagSub (φ : V₁ →ₗ[ℂ] V₂) : Submodule ℂ (sD D₁ D₂) := LinearMap.range (diagι φ)

theorem sE_diagι (φ : V₁ →ₗ[ℂ] V₂) (hst : IsKStableSub ε E₁ V₁)
    (hcomm : ∀ a b (hab : ε a = ε b) (v : V₁),
      E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hst a b hab _ v.2⟩ : V₂) : D₂))
    {a b : Fin n} (hab : ε a = ε b) (v : V₁) :
    sE E₁ E₂ a b (diagι φ v) = diagι φ ⟨E₁ a b v, hst a b hab _ v.2⟩ := by
  rw [diagι_apply, diagι_apply]
  simp only [sE, lift_ofP]
  rw [hcomm a b hab v]

theorem diagSub_isKIrrHW (φ : V₁ →ₗ[ℂ] V₂) {Λ : Fin n → ℝ} (hV₁ : IsKIrrHW ε E₁ Λ V₁)
    (hcomm : ∀ a b (hab : ε a = ε b) (v : V₁),
      E₂ a b ((φ v : V₂) : D₂) = ((φ ⟨E₁ a b v, hV₁.2.1 a b hab _ v.2⟩ : V₂) : D₂)) :
    IsKIrrHW ε (sE E₁ E₂) Λ (diagSub φ) := by
  unfold IsKIrrHW
  have : FiniteDimensional ℂ V₁ := hV₁.1
  have hstab : IsKStableSub ε (sE E₁ E₂) (diagSub φ) := by
    intro a b hab x hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
    rw [sE_diagι φ hV₁.2.1 hcomm hab v]
    exact LinearMap.mem_range_self _ _
  refine ⟨inferInstanceAs (FiniteDimensional ℂ (LinearMap.range (diagι φ))), hstab, ?_, ?_⟩
  · intro S' hS' hS'st
    let T : Submodule ℂ D₁ := (S'.comap (diagι φ)).map V₁.subtype
    have hTle : T ≤ V₁ := by
      intro u hu
      obtain ⟨v, -, rfl⟩ := Submodule.mem_map.mp hu
      exact v.2
    have hTst : IsKStableSub ε E₁ T := by
      intro a b hab u hu
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
      refine Submodule.mem_map.mpr ⟨⟨E₁ a b v, hV₁.2.1 a b hab _ v.2⟩, ?_, rfl⟩
      show diagι φ _ ∈ S'
      rw [← sE_diagι φ hV₁.2.1 hcomm hab v]
      exact hS'st a b hab _ hv
    rcases hV₁.2.2.1 T hTle hTst with hT | hT
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp (hS' hx)
      have hvT : (v : D₁) ∈ T := Submodule.mem_map.mpr ⟨v, hx, rfl⟩
      rw [hT, Submodule.mem_bot] at hvT
      have hv0 : v = 0 := (Submodule.coe_eq_zero).mp hvT
      rw [hv0, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      intro x hx
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
      have hvT : (v : D₁) ∈ T := by
        rw [hT]
        exact v.2
      obtain ⟨v', hv', hvv'⟩ := Submodule.mem_map.mp hvT
      have hv'v : v' = v := Subtype.ext hvv'
      rw [← hv'v]
      exact hv'
  · obtain ⟨w, hwV, hw0, hK⟩ := hV₁.2.2.2
    obtain ⟨hwa, hwb⟩ := hK
    refine ⟨diagι φ ⟨w, hwV⟩, LinearMap.mem_range_self _ _, ?_, ?_⟩
    · intro h
      apply hw0
      have h1 := congrArg (fun x => (toP x).1) h
      simpa [diagι_apply, toPrimitive_ofPrimitive] using h1
    · refine ⟨fun a => ?_, fun a b hab hε => ?_⟩
      · rw [sE_diagι φ hV₁.2.1 hcomm (a := a) (b := a) rfl, ← map_smul]
        congr 1
        exact Subtype.ext (hwa a)
      · rw [sE_diagι φ hV₁.2.1 hcomm hε]
        have h0 : (⟨E₁ a b w, hV₁.2.1 a b hε _ hwV⟩ : V₁) = 0 := Subtype.ext (hwb a b hab hε)
        rw [h0, map_zero]

theorem casimir_diagSub (φ : V₁ →ₗ[ℂ] V₂) {c : ℂ}
    (hc₁ : ∀ v ∈ V₁, casimir E₁ v = c • v) (hc₂ : ∀ v ∈ V₂, casimir E₂ v = c • v) :
    ∀ x ∈ diagSub φ, casimir (sE E₁ E₂) x = c • x := by
  intro x hx
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
  rw [casimir_sE, diagι_apply]
  simp only [lift_ofP]
  rw [hc₁ _ v.2, hc₂ _ (φ v).2, ← Prod.smul_mk, map_smul]

end USum

end ReciprocityTheory.ChartRestriction.DS
