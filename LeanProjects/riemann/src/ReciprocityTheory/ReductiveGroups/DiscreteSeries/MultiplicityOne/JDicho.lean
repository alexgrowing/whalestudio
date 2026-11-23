import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TransposeUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoA

noncomputable section

open MeasureTheory ComplexConjugate
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open ConjugateHilbertSpace

theorem schurDichotomy : SchurDichotomy := by
  intro G _ _ _ _ _ μ _ _ _ H _ _ _ _ θ ρ hθc hθm hθθ hmap hρ1 hρm hiso hcont hsq hirr
  classical
  have hθ1 : θ 1 = 1 := by
    have h := hθm 1 1
    rw [one_mul] at h
    exact mul_left_cancel (a := θ 1) (by rw [mul_one]; exact h.symm)
  have hθinv : ∀ a, θ a⁻¹ = (θ a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_left
    rw [← hθm, mul_inv_cancel, hθ1]
  have hθmp : MeasurePreserving θ μ μ := ⟨hθc.measurable, hmap⟩
  have hR : Formalism.MainNotions.BridgeCSchur.SqRep μ ρ := ⟨hρ1, hρm, hiso, hcont, hsq⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : G → (Cj H →L[ℂ] Cj H),
      ∀ g v, τ g v = toCj (ρ (θ g)⁻¹ (ofCj v)) :=
    ⟨fun g => opCj (ρ (θ g)⁻¹), fun g v => opCj_apply _ _⟩
  have hcoef : ∀ g (v w : Cj H), ⟪w, τ g v⟫_ℂ = ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ := by
    intro g v w
    rw [inner_def, hτ]
    have h := hR.inner_left (θ g)⁻¹ (ofCj v) (ofCj w)
    rw [inv_inv] at h
    exact h
  have hT : Formalism.MainNotions.BridgeCSchur.SqRep μ τ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext v
      simp only [hτ, hθ1, inv_one, hρ1]
      rfl
    · intro a b
      ext v
      simp only [ContinuousLinearMap.comp_apply, hτ]
      rw [hθm, mul_inv_rev, hρm]
      rfl
    · intro g v
      rw [hτ]
      exact hiso _ _
    · intro v
      have e : (fun g => τ g v) = fun g => toCj (ρ (θ g)⁻¹ (ofCj v)) := funext fun g => hτ g v
      rw [e]
      exact (hcont (ofCj v)).comp hθc.inv
    · intro v w
      have e : (fun g => ⟪w, τ g v⟫_ℂ) = fun g => ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ :=
        funext fun g => hcoef g v w
      rw [e]
      exact (hsq (ofCj w) (ofCj v)).comp_measurePreserving hθmp
  have hirrT : ∀ S : Submodule ℂ (Cj H), IsClosed (S : Set (Cj H)) →
      (∀ g, ∀ v ∈ S, τ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS hSi
    let S' : Submodule ℂ H :=
      { carrier := {x | toCj x ∈ S}
        add_mem' := fun ha hb => S.add_mem ha hb
        zero_mem' := S.zero_mem
        smul_mem' := fun c x hx => by
          have h2 := S.smul_mem (conj c) (show toCj x ∈ S from hx)
          rw [smul_def, Complex.conj_conj] at h2
          show toCj (c • x) ∈ S
          exact h2 }
    have hS'c : IsClosed (S' : Set H) := hS.preimage (eCj (H := H)).symm.continuous
    have hS'i : ∀ h, ∀ x ∈ S', ρ h x ∈ S' := by
      intro h x hx
      have h2 := hSi (θ h⁻¹) (toCj x) hx
      rw [hτ, hθθ, inv_inv] at h2
      exact h2
    rcases hirr S' hS'c hS'i with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have h3 : ofCj v ∈ S' := hv
      rw [h, Submodule.mem_bot] at h3
      exact h3
    · right
      rw [eq_top_iff]
      intro v _
      have h3 : ofCj v ∈ S' := by rw [h]; trivial
      exact h3
  by_cases hne : ∃ U : Cj H ≃ₗᵢ[ℂ] H, ∀ g v, U (τ g v) = ρ g (U v)
  · right
    obtain ⟨U, hU⟩ := hne
    refine ⟨((eCj (H := H)).symm.trans U : H ≃ₗᵢ⋆[ℂ] H), ?_, ?_⟩
    · intro g x y
      calc ⟪y, ρ (θ g) x⟫_ℂ = ⟪toCj x, τ g (toCj y)⟫_ℂ := (hcoef g (toCj y) (toCj x)).symm
        _ = ⟪U (toCj x), U (τ g (toCj y))⟫_ℂ := (U.inner_map_map _ _).symm
        _ = ⟪U (toCj x), ρ g (U (toCj y))⟫_ℂ := by rw [hU]
    · intro h v
      have h2 := hU (θ h)⁻¹ (toCj v)
      rw [hτ, hθinv, hθθ, inv_inv] at h2
      exact h2
  · left
    intro x y x' y'
    have h0 := Formalism.MainNotions.BridgeCSchur.schur_orth_ineq hT hR hirrT hirr hne (toCj y) (toCj x) x' y'
    have e : (fun g => ⟪y, ρ (θ g) x⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ) =
        fun g => ⟪toCj x, τ g (toCj y)⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ :=
      funext fun g => congrArg (· * star ⟪y', ρ g x'⟫_ℂ) (hcoef g (toCj y) (toCj x)).symm
    exact (congrArg (fun f => ∫ g, f g ∂μ) e).trans h0

end ReciprocityTheory.ChartRestriction.DS.Mult1
