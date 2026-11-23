import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut1p
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stCut4 (h : UnitaryGroupStructuralFacts) : StCut4 := by
  intro hS k r Wp _ _ _ D hD γ P₁ Q P₂ Q₂ hPQ
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z :=
    ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarW.conc)
  have key : ∀ g ∈ UWset k r D.z, ∀ x y : Wp,
      ⟪P₁ y, D.π g (Q x)⟫_ℂ = ⟪P₂ y, D.π (th k r γ g) (Q₂ x)⟫_ℂ := by
    intro g hg x y
    have e := congrArg (fun T : Wp →L[ℂ] Wp => ⟪y, T x⟫_ℂ) (hPQ g hg)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right] using e
  have hL : ∀ x y ξ η : Wp,
      ∫ g : Mt k r, ⟪P₁ y, D.π (Matrix.of g) (Q x)⟫_ℂ * star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW =
        ⟪η, Q x⟫_ℂ * ⟪P₁ y, ξ⟫_ℂ / (Module.finrank ℂ Wp : ℂ) :=
    fun x y ξ η => hS k r Wp D hD (Q x) (P₁ y) η ξ
  have hE : ∀ x y ξ η : Wp,
      ∫ g : Mt k r, ⟪P₁ y, D.π (Matrix.of g) (Q x)⟫_ℂ * star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW =
        ∫ g : Mt k r, ⟪P₂ y, D.π (th k r γ (Matrix.of g)) (Q₂ x)⟫_ℂ *
          star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW := by
    intro x y ξ η
    refine integral_congr_ae (hW.mono fun g hg => ?_)
    simp only [key _ hg]
  have hdim : (Module.finrank ℂ Wp : ℂ) = 0 → ∀ v : Wp, v = 0 := fun h0 =>
    finrank_zero_iff_forall_zero.1 (by exact_mod_cast h0)
  refine ⟨fun h0 x y ξ η => ?_, fun C₀ hC x y ξ η => ?_⟩
  · have e := (hL x y ξ η).symm.trans ((hE x y ξ η).trans (h0 (Q₂ x) (P₂ y) η ξ))
    by_cases hn : (Module.finrank ℂ Wp : ℂ) = 0
    · simp [hdim hn η]
    · exact (div_eq_zero_iff.1 e).resolve_right hn
  · have e2 : ∫ g : Mt k r, ⟪P₂ y, D.π (th k r γ (Matrix.of g)) (Q₂ x)⟫_ℂ *
          star ⟪ξ, D.π (Matrix.of g) η⟫_ℂ ∂D.μW =
        ⟪η, C₀ (P₂ y)⟫_ℂ * ⟪C₀ (Q₂ x), ξ⟫_ℂ / (Module.finrank ℂ Wp : ℂ) := by
      rw [← hS k r Wp D hD (C₀ (P₂ y)) (C₀ (Q₂ x)) η ξ]
      refine integral_congr_ae (hW.mono fun g hg => ?_)
      simp only [hC _ hg]
    have e := (hL x y ξ η).symm.trans ((hE x y ξ η).trans e2)
    by_cases hn : (Module.finrank ℂ Wp : ℂ) = 0
    · simp [hdim hn η]
    · exact (div_left_inj' hn).1 e

end ReciprocityTheory.ChartRestriction.DS.Mult1
