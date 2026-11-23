import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ProperRatH
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.E1

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def lInt {ι : Type} [Fintype ι] (D : Dom E a b) (k₁ k₂ : H E a b → ι → Hs (ι := ι) D) (τ : ℝ)
    (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (x : H E a b) : ℂ :=
  chiT τ x.1 * chiT τ x.2 * ∑ i, inner ℂ (k₁ x i) (U (k₂ x i))

structure IsVecs {ι : Type} [Fintype ι] (D : Dom E a b) (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ))
    (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (k₁ k₂ : H E a b → ι → Hs (ι := ι) D) : Prop where
  cont : ∀ i, Continuous (fun x => k₁ x i) ∧ Continuous fun x => k₂ x i
  rep₁ : ∀ x i (u : Hs (ι := ι) D), inner ℂ (k₁ x i) u = ∑ j, ∫ y, kerH (Φ₁ i j) x y * (u j : H E a b → ℂ) y ∂D.ν
  rep₂ : ∀ x i (u : Hs (ι := ι) D), inner ℂ u (k₂ x i) =
    ∑ j, ∑ l, ∫ y, starRingEnd ℂ ((u j : H E a b → ℂ) y) * kerH (Φ₂ j l) y (th x) * M l i ∂D.ν
  norm : ∃ (C : ℝ≥0∞) (Ω : Set (H E a b)), C ≠ ⊤ ∧ IsCompact Ω ∧ ∀ x i,
    ‖k₁ x i‖ₑ ^ 2 ≤ C * cnt (ratH E a b) Ω x ∧ ‖k₂ x i‖ₑ ^ 2 ≤ C * cnt (ratH E a b) Ω x
  diag : ∀ (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E a b → ℂ)), IsTestM Φ → IsROp D Φ (T₁ * U * T₂) →
    ∀ x, kerTw2 (fun y => ∑ i, ∑ j, Φ i j y * M j i) x x = ∑ i, inner ℂ (k₁ x i) (U (k₂ x i))

def VecsEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
  (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)) (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ),
  IsTestM Φ₁ → IsTestM Φ₂ → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → ∃ k₁ k₂, IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂

def LBound : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
  (k₁ k₂ : H E a b → ι → Hs (ι := ι) D) (C₀ : ℝ≥0∞) (Ω : Set (H E a b)),
  (∀ i, Continuous (fun x => k₁ x i) ∧ Continuous fun x => k₂ x i) → C₀ ≠ ⊤ → IsCompact Ω →
  (∀ x i, ‖k₁ x i‖ₑ ^ 2 ≤ C₀ * cnt (ratH E a b) Ω x ∧ ‖k₂ x i‖ₑ ^ 2 ≤ C₀ * cnt (ratH E a b) Ω x) →
  ∃ (C : ℝ) (N : ℕ), ∀ τ : ℝ, 0 ≤ τ → ∀ U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D,
    Integrable (lInt D k₁ k₂ τ U) D.ν ∧ ∫ x, ‖lInt D k₁ k₂ τ U x‖ ∂D.ν ≤ C * (1 + τ) ^ N * ‖U‖

def SFun : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
  (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)) (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ),
  IsTestM Φ₁ → IsTestM Φ₂ → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ → ∃ k₁ k₂, IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂ ∧
    ∃ (C : ℝ) (N : ℕ), ∀ τ : ℝ, 0 ≤ τ → ∀ U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D,
      Integrable (lInt D k₁ k₂ τ U) D.ν ∧ ‖∫ x, lInt D k₁ k₂ τ U x ∂D.ν‖ ≤ C * (1 + τ) ^ N * ‖U‖ ∧
      ∀ Φ : Matrix ι ι (H E a b → ℂ), IsTestM Φ → IsROp D Φ (T₁ * U * T₂) →
        ∫ x, chiT τ x.1 * chiT τ x.2 * kerTw2 (fun y => ∑ i, ∑ j, Φ i j y * M j i) x x ∂D.ν = ∫ x, lInt D k₁ k₂ τ U x ∂D.ν

theorem sFun_of (h1 : VecsEx) (h2 : LBound) : SFun := by
  intro E _ _ _ a b D ι _ Φ₁ Φ₂ T₁ T₂ M a1 a2 b1 b2
  obtain ⟨k₁, k₂, hk⟩ := h1 E a b D ι Φ₁ Φ₂ T₁ T₂ M a1 a2 b1 b2
  obtain ⟨C₀, Ω, c1, c2, c3⟩ := hk.norm
  obtain ⟨C, N, h⟩ := h2 E a b D ι k₁ k₂ C₀ Ω hk.cont c1 c2 c3
  refine ⟨k₁, k₂, hk, C, N, fun τ hτ U => ⟨(h τ hτ U).1, (norm_integral_le_integral_norm _).trans (h τ hτ U).2,
    fun Φ d1 d2 => ?_⟩⟩
  simp only [lInt, hk.diag U Φ d1 d2]

theorem sb_of (h : SFun) : SB := by
  intro E _ _ _ a b D ι _ Φ₁ Φ₂ T₁ T₂ M a1 a2 b1 b2
  obtain ⟨k₁, k₂, -, C, N, h⟩ := h E a b D ι Φ₁ Φ₂ T₁ T₂ M a1 a2 b1 b2
  exact ⟨C, N, fun τ U Φ hτ d1 d2 => ((h τ hτ U).2.2 Φ d1 d2).symm ▸ (h τ hτ U).2.1⟩

end PositivityTheory.Rg.BcB.E1

end
