import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF.KeyArch

theorem pos_of_isArchNorm (hU : ThetaUnifAV) (x : KeyIn ℂ) {nth nη : ℝ} (h : KeyPow.IsArchNorm x nth nη) :
    0 < nth ∧ 0 < nη := by
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  obtain ⟨u', τ, M, a, b, c, -, -, -, -, -, -, -, -, -, -, e⟩ :=
    keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have p₁ : 0 ≤ nth :=
    h₆ ▸ div_nonneg (MeasureTheory.integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg
  have p₂ : 0 ≤ nη := h₇ ▸ by positivity
  have hne : ‖M.det ^ 4 / c ^ 8‖ * nth ^ 4 * nη ^ 2 ≠ 0 := by
    rw [e]; have := Real.pi_pos; positivity
  have q₁ := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have q₂ := right_ne_zero_of_mul hne
  exact ⟨p₁.lt_of_ne' fun h0 => q₁ (by rw [h0]; norm_num), p₂.lt_of_ne' fun h0 => q₂ (by rw [h0]; norm_num)⟩

theorem exists_pos_keyArchAt : ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (σ : K →+* ℂ), ∃ t n : ℝ, 0 < t ∧ 0 < n ∧ ∀ T abelian₂ : MLine K, T.n σ = t → abelian₂.n σ = n → KeyArchAt x T abelian₂ σ := by
  intro hU K _ _ x σ
  obtain ⟨x', hx⟩ := KeyPow.exists_keyPB x σ
  obtain ⟨nth, nη, h⟩ := KeyPow.exists_isArchNorm hU x'
  obtain ⟨p₁, p₂⟩ := pos_of_isArchNorm hU x' h
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨Real.sqrt nth, Real.sqrt nη⁻¹, Real.sqrt_pos.2 p₁, Real.sqrt_pos.2 (inv_pos.2 p₂), fun T abelian₂ hT hL =>
    ⟨x', u, Hm, W, χ, θ, Fd, hx, h₁, h₂, h₃, h₄, h₅, ?_, ?_⟩⟩
  · rw [hT, Real.sq_sqrt p₁.le, h₆]
  · rw [hL, Real.sq_sqrt (inv_pos.2 p₂).le, h₇, inv_div]

end GlobalTheory.LamF.KeyArch
end
