import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.R
open scoped ValuativeRel ComplexConjugate

namespace GlobalTheory.CompanionTheory.RankinSelberg

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

instance sFinite_plane_measure (ψ : AddChar F Circle) : SFinite (m2 ψ) := by unfold m2; infer_instance

theorem isUnit1_inv {c : Fˣ →* ℂˣ} (h : IsUnit1 c) : IsUnit1 c⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · have : ((c⁻¹ : Fˣ →* ℂˣ) : Fˣ → ℂˣ) = fun x => (c x)⁻¹ := rfl
    rw [this]
    exact h.1.inv
  · have h1 := h.2 x
    simp [MonoidHom.inv_apply, h1]

theorem isUnit1_mul {c d : Fˣ →* ℂˣ} (h : IsUnit1 c) (h' : IsUnit1 d) : IsUnit1 (c * d) := by
  refine ⟨?_, fun x => ?_⟩
  · have : ((c * d : Fˣ →* ℂˣ) : Fˣ → ℂˣ) = fun x => c x * d x := rfl
    rw [this]
    exact h.1.mul h'.1
  · simp [MonoidHom.mul_apply, h.2 x, h'.2 x]

theorem strip_one_sub {s : ℂ} (h : Strip s) : Strip (1 - s) := by
  obtain ⟨h0, h1⟩ := h
  constructor <;> simp <;> linarith

theorem char_neg_one_inv (μ : Fˣ →* ℂˣ) : (μ (-1))⁻¹ = μ (-1) := by
  rw [inv_eq_iff_mul_eq_one, ← map_mul]
  simp

theorem sign_quot (μ₁ μ₂ : Fˣ →* ℂˣ) : (((μ₂ * μ₁⁻¹) (-1) : ℂˣ) : ℂ) = (((μ₁ * μ₂) (-1) : ℂˣ) : ℂ) := by
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, char_neg_one_inv, mul_comm]

theorem whittaker_right_unipotent_translate {ψ : AddChar F Circle} {μ₁ μ₂ : Fˣ →* ℂˣ} {φ : (Fin 2 → F) → ℂ} {x : F} (hA : ∀ g, W2 ψ μ₁ μ₂ φ (g * uni2 x) =
      ((μ₂ (GeneralLinearGroup.det (uni2 x)) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det (uni2 x)) (1 / 2) *
        W2 ψ μ₁ μ₂ (fun r => φ (r ᵥ* ((uni2 x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))) g) :
    (fun g => W2 ψ μ₁ μ₂ φ (g * uni2 x)) =
      W2 ψ μ₁ μ₂ (fun r => φ (r ᵥ* ((uni2 x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))) := by
  have hdet : GeneralLinearGroup.det (uni2 x : GL (Fin 2) F) = 1 := by
    ext; simp [uni2, Matrix.det_fin_two]
  funext g
  rw [hA g, hdet]
  simp [mp, modulus_one]

theorem tri_reorder (ψ : AddChar F Circle) (ν c : Fˣ →* ℂˣ) (s : ℂ) (φ₁ Ψ φ₃ : (Fin 2 → F) → ℂ)
    (hint : Integrable (triI ν c s φ₁ Ψ φ₃) ((m2 ψ).prod ((m2 ψ).prod (m2 ψ)))) :
    ∫ p, triI ν c s φ₁ Ψ φ₃ p ∂((m2 ψ).prod ((m2 ψ).prod (m2 ψ))) =
      ∫ q : (Fin 2 → F) × (Fin 2 → F), φ₁ q.1 * conj (φ₃ q.2) * ∫ r, Ψ r * Kr ν c s q.1 r q.2 ∂m2 ψ
        ∂((m2 ψ).prod (m2 ψ)) := by
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [triI]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only
  ring

end Loc

theorem a9_of_a0_a1_eigenbasis_a6 : Ad3.R.A1 → Ad3.R.A6 → Ad3.R.A8 → Ad3.R.LocalGammaFunctionalEquation → Ad3.R.A9 := by
  intro h1 h6 h8 h9
  intro F _ _ _ _ _ _ ψ hψ _ _ m _ _ μ₁ μ₂ c u₁ u₂ uc φ₁ Ψ hφ hΨ x s hs
  obtain ⟨C, -, hC⟩ := h6 F ψ hψ m
  have hA := h1 F ψ hψ μ₁ μ₂ φ₁ (uni2 x) hφ
  obtain ⟨hφ₃, -, -, hW⟩ := hA
  have hsF : SB (sF ψ Ψ) := (h1 F ψ hψ μ₁ μ₂ Ψ 1 hΨ).2.1
  rw [whittaker_right_unipotent_translate hW]
  set φ₃ : (Fin 2 → F) → ℂ := fun r => φ₁ (r ᵥ* ((uni2 x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) with hφ₃def
  have uci : IsUnit1 c⁻¹ := isUnit1_inv uc
  have hs' : Strip (1 - s) := strip_one_sub hs
  obtain ⟨-, e1⟩ := hC μ₁ μ₂ c u₁ u₂ uc φ₁ φ₃ Ψ hφ hφ₃ hΨ s hs
  obtain ⟨i2, e2⟩ := hC μ₁ μ₂ c⁻¹ u₁ u₂ uci φ₁ φ₃ (sF ψ Ψ) hφ hφ₃ hsF (1 - s) hs'
  obtain ⟨i1, -⟩ := hC μ₁ μ₂ c u₁ u₂ uc φ₁ φ₃ Ψ hφ hφ₃ hΨ s hs
  set ν : Fˣ →* ℂˣ := μ₂ * μ₁⁻¹ with hν
  have uν : IsUnit1 ν := isUnit1_mul u₂ (isUnit1_inv u₁)
  have hg := (h9 F ψ hψ c uc).2 s hs
  have h8' := h8 F ψ hψ ν c uν uc Ψ hΨ s hs
  rw [tri_reorder ψ ν c s φ₁ Ψ φ₃ i1] at e1
  rw [tri_reorder ψ ν c⁻¹ (1 - s) φ₁ (sF ψ Ψ) φ₃ i2] at e2
  simp only [h8'] at e2
  have hconst : ∀ q : (Fin 2 → F) × (Fin 2 → F),
      φ₁ q.1 * conj (φ₃ q.2) * (gam ψ (ν * c) s * gam ψ (ν⁻¹ * c) s * (((ν * c) (-1) : ℂˣ) : ℂ) *
        ∫ r, Ψ r * Kr ν c s q.1 r q.2 ∂m2 ψ) =
      gam ψ (ν * c) s * gam ψ (ν⁻¹ * c) s * (((ν * c) (-1) : ℂˣ) : ℂ) *
        (φ₁ q.1 * conj (φ₃ q.2) * ∫ r, Ψ r * Kr ν c s q.1 r q.2 ∂m2 ψ) := fun q => by ring
  simp only [hconst] at e2
  rw [integral_const_mul] at e2
  rw [e1, e2]
  have hνi : (μ₁ * μ₂⁻¹)⁻¹ = ν := by
    rw [hν, mul_inv, inv_inv, mul_comm]
  have hνi' : μ₁ * μ₂⁻¹ = ν⁻¹ := by rw [← hνi, inv_inv]
  have hsign : (((ν * c) (-1) : ℂˣ) : ℂ) = (((μ₁ * μ₂) (-1) : ℂˣ) : ℂ) * ((c (-1) : ℂˣ) : ℂ) := by
    rw [MonoidHom.mul_apply, Units.val_mul, hν, sign_quot]
  have hss : (1 : ℂ) - (1 - s) = s := by ring
  simp only [gam3, hνi', inv_inv, hss, hsign, ← hg]
  ring

end GlobalTheory.CompanionTheory.RankinSelberg
