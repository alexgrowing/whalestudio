import Formalism.RealPlaceAnalysis.SmoothOnGVIff

open MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.REAL

def eqvSub {n : ℕ} {ε : Fin n → Bool} (S : Subgroup (UJ ε)) (E : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (σ : S → E →ₗᵢ[ℂ] E) :
    Submodule ℂ (UJ ε → E) where
  carrier := {F | ∀ (s : S) (g : UJ ε), F ((s : UJ ε) * g) = σ s (F g)}
  add_mem' := by
    intro F F' hF hF' s g
    simp [hF s g, hF' s g]
  zero_mem' := by
    intro s g
    simp
  smul_mem' := by
    intro c F hF s g
    simp [hF s g]

structure HidaSetting (n : ℕ) (ε : Fin n → Bool) where
  E : Type
  [ng : NormedAddCommGroup E]
  [ips : InnerProductSpace ℂ E]
  [cs : CompleteSpace E]
  S : Subgroup (UJ ε)
  σ : S → E →ₗᵢ[ℂ] E
  ν : Measure (UJ ε)

attribute [instance] HidaSetting.ng HidaSetting.ips HidaSetting.cs

def HidaSetting.adm {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) : Submodule ℂ (UJ ε → P.E) :=
  eqvSub P.S P.E P.σ

def Rs {n : ℕ} {ε : Fin n → Bool} {E : Type*} (h : UJ ε) (F : UJ ε → E) : UJ ε → E :=
  fun g => F (g * h)

def IsRightTranslationIsometric {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) : Prop :=
  ∀ F ∈ P.adm, StronglyMeasurable F → ∀ h : UJ ε,
    ∫⁻ g, ‖Rs h F g‖ₑ ^ 2 ∂P.ν = ∫⁻ g, ‖F g‖ₑ ^ 2 ∂P.ν

def IsSettingL2 {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) (F : UJ ε → P.E) : Prop :=
  F ∈ P.adm ∧ StronglyMeasurable F ∧ ∫⁻ g, ‖F g‖ₑ ^ 2 ∂P.ν < ∞

def sInner {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) (F F' : UJ ε → P.E) : ℂ :=
  ∫ g, ⟪F g, F' g⟫_ℂ ∂P.ν

def Rconv {n : ℕ} {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (φ : UJ ε → ℂ) (F : UJ ε → E) : UJ ε → E :=
  fun g => ∫ h, φ h • F (g * h) ∂(muG ε)

def settingG {n : ℕ} (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : HidaSetting n ε :=
  { E := E, S := ⊥, σ := fun _ => LinearIsometry.id, ν := muG ε }

def settingQ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (UJ ε)) (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (σ : S → E →ₗᵢ[ℂ] E) (ph : UJ ε → ℝ≥0∞) : HidaSetting n ε :=
  { E := E, S := S, σ := σ, ν := (muG ε).withDensity ph }

lemma mem_admissible_setting {n : ℕ} (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (F : UJ ε → E) : F ∈ (settingG ε E).adm := by
  intro s g
  have hs : (s : UJ ε) = 1 := Subgroup.mem_bot.mp s.2
  simp only [settingG, hs, one_mul]
  rfl

lemma rs_mem_adm {n : ℕ} {ε : Fin n → Bool} (P : HidaSetting n ε) (F : UJ ε → P.E) (hF : F ∈ P.adm)
    (h : UJ ε) : Rs h F ∈ P.adm := by
  intro s g
  simp only [Rs, mul_assoc]
  exact hF s (g * h)

lemma rs_mul {n : ℕ} {ε : Fin n → Bool} {E : Type*} (h₁ h₂ : UJ ε) (F : UJ ε → E) :
    Rs (h₁ * h₂) F = Rs h₁ (Rs h₂ F) := by
  funext g
  simp only [Rs, mul_assoc]

def LogLogRegularisationSetting : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
    IsRightTranslationIsometric (settingG ε E)

def QuotientSetting : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (UJ ε)) (muS : Measure S) (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (σ : S → E →ₗᵢ[ℂ] E) (ph : UJ ε → ℝ≥0∞),
    SFinite muS → muS.IsMulLeftInvariant → Measure.map (fun s : S => s⁻¹) muS = muS → Measurable ph →
    (∀ᵐ g ∂(muG ε), ∫⁻ s, ph ((s : UJ ε) * g) ∂muS = 1) →
    IsRightTranslationIsometric (settingQ ε S E σ ph)

def SettingHilbertFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : HidaSetting n ε), IsRightTranslationIsometric P →
    ∀ (F F' : UJ ε → P.E) (h : UJ ε) (c : ℂ), IsSettingL2 P F → IsSettingL2 P F' →
      IsSettingL2 P (Rs h F) ∧ IsSettingL2 P (F + F') ∧ IsSettingL2 P (c • F) ∧
      Integrable (fun g => ⟪F g, F' g⟫_ℂ) P.ν ∧
      sInner P F F = (((∫⁻ g, ‖F g‖ₑ ^ 2 ∂P.ν).toReal : ℝ) : ℂ) ∧
      sInner P F' F = starRingEnd ℂ (sInner P F F') ∧
      ‖sInner P F F'‖ ^ 2 ≤ (sInner P F F).re * (sInner P F' F').re ∧
      sInner P (Rs h F) (Rs h F') = sInner P F F'

def RconvAdm : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : HidaSetting n ε) (φ : UJ ε → ℂ) (F : UJ ε → P.E),
    F ∈ P.adm → Rconv φ F ∈ P.adm

end Formalism.REAL
