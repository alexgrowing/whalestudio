import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr

namespace GlobalTheory.RegEst

variable {e : ℕ} {ι : Type} [Fintype ι] {N : ℕ}

def InSPart (M : Man e) (Q : (ι → Fin N → ℝ) → ℝ → ℝ → ℝ → Fin (M.n + 1) → Prop) : Prop :=
  ∃ s₀ : ℝ, 0 < s₀ ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ u, Dom u → ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ l : ℝ, l = (s ^ 2)⁻¹ →
    ∀ σ, Q u s l C σ

def CurvPart {M : Man e} (F : An M ι N) : Prop := InSPart M fun u s l C σ =>
  (M.A σ).Smooth (F.phS u s σ) ∧
    IsPsh (M.A σ) (F.th u σ + LocPot.ofFun (F.phS u s σ) + (M.Om σ).rsmul (C * ‖u‖ * (Real.log l / l)))

def BdPart {M : Man e} (F : An M ι N) : Prop := InSPart M fun u s l C σ => ∀ x,
  (-(C * ‖u‖ * Real.log l) - C * ‖u‖ ≤ F.phS u s σ x ∧ F.phS u s σ x ≤ C * ‖u‖) ∧
    (x ∉ M.Z σ → F.ph u σ x ≤ F.phS u s σ x)

def ClosePart {M : Man e} (F : An M ι N) : Prop := InSPart M fun u s l C σ => ∀ x, x ∉ M.Z σ →
  (M.r σ x ≤ l → F.phS u s σ x ≤ F.ph u σ x + C * ‖u‖ * Real.exp (-l / 3) + C * ‖u‖ * (Real.log l / l)) ∧
    F.phS u s σ x ≤ F.ph u σ x + C * ‖u‖ * Real.exp (-l / 3) + C * ‖u‖ * (Real.log l / l) * M.r σ x

theorem inS_of_parts {M : Man e} (F : An M ι N) (h₁ : CurvPart F) (h₂ : BdPart F) (h₃ : ClosePart F) : F.InS := by
  obtain ⟨s₁, hs₁, C₁, h₁⟩ := h₁
  obtain ⟨s₂, hs₂, C₂, h₂⟩ := h₂
  obtain ⟨s₃, hs₃, C₃, h₃⟩ := h₃
  refine ⟨min (min s₁ s₂) s₃, lt_min (lt_min hs₁ hs₂) hs₃, max (max C₁ C₂) C₃, fun u hu s hs hs' l hl σ => ?_⟩
  have a₁ : s ≤ s₁ := hs'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have a₂ : s ≤ s₂ := hs'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have a₃ : s ≤ s₃ := hs'.trans (min_le_right _ _)
  have b₁ : C₁ ≤ max (max C₁ C₂) C₃ := (le_max_left _ _).trans (le_max_left _ _)
  have b₂ : C₂ ≤ max (max C₁ C₂) C₃ := (le_max_right _ _).trans (le_max_left _ _)
  have b₃ : C₃ ≤ max (max C₁ C₂) C₃ := le_max_right _ _
  obtain ⟨k₁, k₂⟩ := h₁ _ b₁ u hu s hs a₁ l hl σ
  refine ⟨k₁, k₂, fun x => ⟨(h₂ _ b₂ u hu s hs a₂ l hl σ x).1, fun hx => ⟨(h₂ _ b₂ u hu s hs a₂ l hl σ x).2 hx, ?_⟩⟩⟩
  exact h₃ _ b₃ u hu s hs a₃ l hl σ x hx

end GlobalTheory.RegEst

end
