import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj

namespace GlobalTheory

theorem eigenCoord_top_of_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ τ (i : Fin (Dw.mult τ)), ∃ cf : Fin (Dw.mult τ) → ℂ, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ eb e τ i = h (∑ j, cf j • eb e τ j)) → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), (∀ j, j ≤ i) → ∃ y : ℂ, ∀ w, h w (e.symm ⟨τ, i⟩) = y * w (e.symm ⟨τ, i⟩) := by
  intro E _ _ _ H Dw g e h hyp τ i htop
  have inv : ∀ τ' (i' : Fin (Dw.mult τ')), ∃ cf : Fin (Dw.mult τ') → ℂ, IsUnit (cf i') ∧
      (∀ j, i' < j → cf j = 0) ∧ h.symm (eb e τ' i') = ∑ j, cf j • eb e τ' j := by
    intro τ' i'
    obtain ⟨cf, hu, hz, he⟩ := hyp τ' i'
    exact ⟨cf, hu, hz, by rw [he, LinearEquiv.symm_apply_apply]⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = h.symm (eb e τ i) (e.symm ⟨τ, i⟩) := ⟨_, rfl⟩
  have hcu : c ≠ 0 := by
    obtain ⟨cf, hu, -, he⟩ := inv τ i
    rw [hc, he, sum_eb_apply]
    exact hu.ne_zero
  have letter : ∀ τ' (i' : Fin (Dw.mult τ')),
      h.symm (eb e τ' i') (e.symm ⟨τ, i⟩) = c * eb e τ' i' (e.symm ⟨τ, i⟩) := by
    intro τ' i'
    by_cases hτ : τ' = τ
    · subst hτ
      by_cases hi : i' = i
      · subst hi
        rw [← hc, eb_apply, if_pos rfl, mul_one]
      · obtain ⟨cf, -, hz, he⟩ := inv τ' i'
        have hlt : i' < i := lt_of_le_of_ne (htop i') hi
        have hne : (⟨τ', i⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≠ ⟨τ', i'⟩ := by
          intro hq
          exact hi (eq_of_heq (Sigma.mk.inj_iff.mp hq).2).symm
        rw [he, sum_eb_apply, hz i hlt, eb_apply, if_neg hne, mul_zero]
    · obtain ⟨cf, -, -, he⟩ := inv τ' i'
      have hz : ∀ j : Fin (Dw.mult τ'), eb e τ' j (e.symm ⟨τ, i⟩) = 0 := by
        intro j
        rw [eb_apply, if_neg]
        intro hq
        exact hτ (Sigma.mk.inj_iff.mp hq).1.symm
      rw [he, Finset.sum_apply, hz i', mul_zero]
      exact Finset.sum_eq_zero fun j _ => by simp [hz j]
  have key : ∀ u : Fin g → ℂ, h.symm u (e.symm ⟨τ, i⟩) = c * u (e.symm ⟨τ, i⟩) := by
    have hL : (LinearMap.proj (e.symm ⟨τ, i⟩) : (Fin g → ℂ) →ₗ[ℂ] ℂ) ∘ₗ h.symm.toLinearMap =
        c • (LinearMap.proj (e.symm ⟨τ, i⟩) : (Fin g → ℂ) →ₗ[ℂ] ℂ) := by
      refine LinearMap.pi_ext fun p x => ?_
      have hp : (Pi.single p x : Fin g → ℂ) = x • eb e (e p).1 (e p).2 := by
        funext r
        simp [eb, Pi.single_apply]
      rw [hp, map_smul, map_smul]
      have := letter (e p).1 (e p).2
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply, LinearMap.smul_apply,
        smul_eq_mul, this]
    intro u
    simpa using LinearMap.congr_fun hL u
  refine ⟨c⁻¹, fun w => ?_⟩
  have := key (h w)
  rw [LinearEquiv.symm_apply_apply] at this
  rw [this, inv_mul_cancel_left₀ hcu]

end GlobalTheory
