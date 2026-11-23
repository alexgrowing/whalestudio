import Mathlib
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignatureAndNodeGaps

def NodeGapGe (D : D7) (h₀ : ℝ) : Prop :=
  ∀ (τ : D.what₂.Tau) (i : ℕ) (h : i + 1 < D.R.m),
    h₀ ≤ (((D.hc τ).b ⟨i + 1, h⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ)

def SizeRows (D : D7) (h₀ : ℝ) : Prop :=
  NodeGapGe D h₀ ∧
  2 * ((D.R.r + D.R.m * D.R.t : ℕ) : ℝ) ^ 3 + (D.R.t : ℝ) + 3 ≤ h₀ ∧
  1800 < D.R.r + D.R.m * D.R.t

def ChainParOfSizes : Prop :=
  ∀ (D : D7) (h₀ : ℝ), SizeRows D h₀ → ∀ k : Fin D.R.m, GlobalTheory.Chain.ChainPar D k

def SignatureAndGaps : Prop :=
  ∀ (D : D7) (h₀ : ℝ), SizeRows D h₀ → ∀ j : ℕ, j ≤ D.R.m → ∀ τ : D.what₂.Tau,
    ((parA (Ptw D) j τ).filter fun x => x.2 = false).card = (D.R.m - j) / 2 ∧
    ((parA (Ptw D) j τ).filter fun x => x.2 = true).card + (D.R.m - j) / 2 = D.R.r + j * D.R.t ∧
    ∀ x ∈ parA (Ptw D) j τ, ∀ y ∈ parA (Ptw D) j τ, x.2 ≠ y.2 → h₀ ≤ |((x.1 - y.1 : ℚ) : ℝ)|

example (D : D7) (h₀ : ℝ) (h : SizeRows D h₀) (τ : D.what₂.Tau) :
    2 * (1800 : ℝ) ^ 3 <
      (((D.hc τ).b ⟨0 + 1, D.R.two_le_m⟩ - (D.hc τ).b ⟨0, by have := D.R.two_le_m; omega⟩ : ℚ) : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := h
  have h4 := h1 τ 0 D.R.two_le_m
  have h5 : (1800 : ℝ) < ((D.R.r + D.R.m * D.R.t : ℕ) : ℝ) := by exact_mod_cast h3
  have h6 : (1800 : ℝ) ^ 3 < ((D.R.r + D.R.m * D.R.t : ℕ) : ℝ) ^ 3 :=
    pow_lt_pow_left₀ h5 (by norm_num) (by norm_num)
  have h7 : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

end GlobalTheory.IndefiniteRowSideFullHecke.SignatureAndNodeGaps

end
