import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeLocGeo

open Matrix

def modelFrame {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ :=
  fromBlocks 1 0 Z 1

def modelHodgeGram {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ :=
  (modelFrame Z)ᵀ * fromBlocks (-1) 0 0 1 * (modelFrame Z)ᴴᵀ

def wLine (c : ℝ) {p q : ℕ} (G : Matrix (Fin p) (Fin p) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  (c : ℂ) • (G * (1 - Z.map (starRingEnd ℂ) * Zᵀ)⁻¹ * Gᴴ)

def oLine (c : ℝ) {p q : ℕ} (G : Matrix (Fin q) (Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  (c : ℂ) • (G * (1 - Zᴴ * Z)⁻¹ * Gᴴ)

def rootNorm (N j : ℕ) (cW cΩ : ℝ) (GW : Matrix (Fin j) (Fin j) ℂ) (GΩ : Matrix (Fin (N - j)) (Fin (N - j)) ℂ)
    (Z : Matrix (Fin j) (Fin (N - j)) ℂ) (i : Fin N) : ℝ :=
  if hi : (i : ℕ) < j then GlobalTheory.GradedNorm.grSq (wLine cW GW Z) ⟨i, hi⟩
  else (GlobalTheory.GradedNorm.grSq (oLine cΩ GΩ Z) ⟨N - 1 - i, by have := i.isLt; omega⟩)⁻¹

example {p q : ℕ} : modelHodgeGram (0 : Matrix (Fin p) (Fin q) ℂ) = fromBlocks (-1) 0 0 1 := by
  simp [modelHodgeGram, modelFrame]

end GlobalTheory.HodgeLocGeo
