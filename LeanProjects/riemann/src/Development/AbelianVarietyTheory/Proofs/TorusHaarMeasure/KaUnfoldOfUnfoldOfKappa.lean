import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kaUnfold_of_unfold_of_kappa :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → (KaUnfoldStatement (E := E)) := by
  intro hU hK r X x0 ho hP FF hFF bb hbb
  obtain ⟨κ, hκm, hκ1, hκB, hκka, ⟨C, hC, hsum⟩, -⟩ := hK r X x0 ho hP bb hbb
  refine ⟨C, hC, fun φ hφm hφB hφΓ => ?_⟩
  have h1 : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, ENNReal.ofReal (κ (cpt X x0 z)) * φ (cpt X x0 z) ∂muF X x0 :=
    lintegral_congr_ae ((OntoH.ae_mem_Om X x0).mono fun z hz => by simp only [hκka z hz])
  have h2 := hU r X x0 ho FF hFF (fun x => ENNReal.ofReal (κ x) * φ x)
    (hκm.ennreal_ofReal.mul hφm) (fun x hx b hb => by simp only [hκB x hx b hb, hφB x hx b hb])
  rw [h1, h2, ← lintegral_const_mul' _ _ hC.ne]
  refine setLIntegral_mono' hFF.1 fun z hz => ?_
  have hx : cpt X x0 z ∈ X.dom := hFF.2.1 hz
  calc ∑' γ : X.Γ, ENNReal.ofReal (κ (lact γ.1 (cpt X x0 z))) * φ (lact γ.1 (cpt X x0 z))
      ≤ ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 (cpt X x0 z)))) * φ (cpt X x0 z) := by
        refine ENNReal.tsum_le_tsum fun γ => ?_
        rw [hφΓ γ.1 γ.2 _ hx]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        obtain ⟨h0, h1⟩ := hκ1 _ (OntoS.dom_lact X γ.2 hx)
        rw [Real.le_sqrt h0.le h0.le]
        nlinarith
    _ = (∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 (cpt X x0 z))))) * φ (cpt X x0 z) :=
        ENNReal.tsum_mul_right
    _ ≤ C * φ (cpt X x0 z) := mul_le_mul' (hsum _ hx) le_rfl

end GlobalTheory
