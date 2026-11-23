import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Transport

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] {ε : Fin n → Bool}
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

theorem dsu_kset_subset (ε : Fin n → Bool) : Formalism.REAL.Kset ε ⊆ Formalism.MainNotions.S.UJset ε := by
  intro g hg
  have h1 : gᴴ * g = 1 := Matrix.mem_unitaryGroup_iff'.1 hg.1
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

abbrev dsuL (U : H₁ ≃ₗᵢ[ℂ] H₂) : H₁ →ₗ[ℂ] H₂ := (U.toLinearEquiv : H₁ →ₗ[ℂ] H₂)

theorem dsu_symm_intertwines (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hU : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) :
    ∀ g ∈ Formalism.REAL.Kset ε, ∀ y, U.symm (σ₂ g y) = σ₁ g (U.symm y) := by
  intro g hg y
  apply U.injective
  rw [hU g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

theorem dsu_kStable_map (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hU : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) {S : Submodule ℂ H₁}
    (hS : Formalism.MainNotions.S.IsKStableOn ε σ₁ S) : Formalism.MainNotions.S.IsKStableOn ε σ₂ (S.map (dsuL U)) := by
  rintro g hg _ ⟨x, hx, rfl⟩
  exact ⟨σ₁ g x, hS g hg x hx, hU g hg x⟩

theorem dsu_isWtOn_map (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hU : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) {μ : Fin n → ℝ} {v : H₁}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ₁ μ v) : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ₂ μ (U v) := by
  intro θ hθ
  rw [← hU _ hθ, hv θ hθ, map_smul]

theorem dsu_isKTypeOf_map (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hU : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) {Λ : Fin n → ℝ} {S : Submodule ℂ H₁}
    (hS : Formalism.MainNotions.S.IsKTypeOf ε σ₁ Λ S) : Formalism.MainNotions.S.IsKTypeOf ε σ₂ Λ (S.map (dsuL U)) := by
  have hU' := dsu_symm_intertwines U hU
  obtain ⟨hfd, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  refine ⟨inferInstance, dsu_kStable_map U hU hst, ?_, ⟨U v, ⟨v, hvS, rfl⟩, ?_, dsu_isWtOn_map U hU hvw⟩, ?_⟩
  · intro S' hle hst'
    have hst'' := dsu_kStable_map U.symm hU' hst'
    have hle' : S'.map (dsuL U.symm) ≤ S := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hle hy
      show U.symm (U x) ∈ S
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact hx
    have hback : (S'.map (dsuL U.symm)).map (dsuL U) = S' := by
      ext y
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        show U (U.symm z) ∈ S'
        rw [LinearIsometryEquiv.apply_symm_apply]
        exact hz
      · intro hy
        exact ⟨U.symm y, ⟨y, hy, rfl⟩, U.apply_symm_apply y⟩
    rcases hirr _ hle' hst'' with h | h
    · left
      rw [← hback, h, Submodule.map_bot]
    · right
      rw [← hback, h]
  · intro h
    exact hv0 (U.injective (h.trans (map_zero U).symm))
  · rintro μ _ ⟨x, hx, rfl⟩ hx0 hw
    refine hdom μ x hx (fun h => hx0 (by simp [h])) ?_
    have := dsu_isWtOn_map U.symm hU' hw
    simpa using this

theorem dsu_lowKSub_map (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hU : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) (lam : Fin n → ℝ) {x : H₁}
    (hx : x ∈ Formalism.MainNotions.S.lowKSub ε lam σ₁) : U x ∈ Formalism.MainNotions.S.lowKSub ε lam σ₂ := by
  have hle : Formalism.MainNotions.S.lowKSub ε lam σ₁ ≤ (Formalism.MainNotions.S.lowKSub ε lam σ₂).comap (dsuL U) := by
    refine sSup_le fun S hS => ?_
    rw [← Submodule.map_le_iff_le_comap]
    exact le_sSup (dsu_isKTypeOf_map U hU hS)
  exact hle hx

end Transport

theorem dsUniv (n : ℕ) : DSUnivStatement n := by
  intro ε lam hlam h hgap H₁ _ _ _ σ₁ H₂ _ _ _ σ₂ hDS₁ hDS₂ w₁ hw₁
  have hh : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h := by
    have h1 : 2 + max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) ≤ hNeed ε :=
      le_max_left _ _
    have h2 := le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
    linarith [hgap.2.2]
  obtain ⟨U, hU⟩ := (isDS_props_of_gap n ε lam hlam h hgap.2.1 hh H₁ σ₁ hDS₁).2.2.2.2 H₂ σ₂ hDS₂
  have hUK : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x) :=
    fun g hg x => hU g (dsu_kset_subset ε hg) x
  refine ⟨U w₁, ⟨by rw [LinearIsometryEquiv.norm_map]; exact hw₁.1, dsu_lowKSub_map U hUK lam hw₁.2⟩, ?_⟩
  intro g hg
  rw [← hU g hg, LinearIsometryEquiv.inner_map_map]

end ReciprocityTheory.ChartRestriction.DS.Lap
