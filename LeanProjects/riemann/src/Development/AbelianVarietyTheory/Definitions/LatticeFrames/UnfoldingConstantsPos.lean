import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealisedChainTorusEq

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace

variable (D : D7) (u : D.what₂.Word)

def d0 : ℕ := Module.finrank ℂ (D.s.Cu u)

def hsDev : ℝ := hsNormSq (Kmat D.s u u - ContinuousLinearMap.id ℂ (D.s.Cu u))

def DiagS (e : ℝ) : Prop := hsDev D u ≤ e * (d0 D u : ℝ)

def SAbs (Γ₀ : ℝ) : Prop := hsDev D u ≤ Γ₀ * (d0 D u : ℝ) ^ 2 / D.what₂.Dstar + (d0 D u : ℝ) / 4

def rkP : ℕ := Module.finrank ℂ (LinearMap.range (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH))

abbrev Desc : Type := (D.mem u).P.Mt →ₗ⋆[ℂ] D.s.HH

def MIMap (Θ : Desc D u) : Prop :=
  ∃ (s l : ℂ) (FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u), l ≠ 0 ∧ Function.Injective FF ∧
    ∀ (φ : (D.mem u).A.Mram) (F : (D.mem u).P.Mt),
      s * PhiC (D.mem u).C (D.mem u).A (D.mem u).P φ F = l * ⟪Θ F, D.s.Pu u (FF φ)⟫_ℂ

def MIKer (Θ : Desc D u) : Prop :=
  ∃ FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u, Function.Injective FF ∧
    ∀ φ : (D.mem u).A.Mram, PhiC (D.mem u).C (D.mem u).A (D.mem u).P φ = 0 →
      ∀ F : (D.mem u).P.Mt, ⟪Θ F, D.s.Pu u (FF φ)⟫_ℂ = 0

def OntoAll (Θ : Desc D u) : Prop := Function.Surjective Θ

def OntoP (Θ : Desc D u) : Prop := ∀ x : D.s.Cu u, (∀ F, ⟪Θ F, D.s.Pu u x⟫_ℂ = 0) → D.s.Pu u x = 0

def KerIncl : Prop :=
  ∃ FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u, Function.Injective FF ∧
    ∀ φ : (D.mem u).A.Mram, PhiC (D.mem u).C (D.mem u).A (D.mem u).P φ = 0 → D.s.Pu u (FF φ) = 0

def RamShare : Prop :=
  (dU D u : ℝ) = (d0 D u : ℝ) * (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f

def RamBig (δ : ℝ) : Prop := 0 < dU D u ∧ (1 - δ) * (d0 D u : ℝ) ≤ (dU D u : ℝ)

def UnfoldingConstantsPos : Prop := 0 < c0 D.s u

theorem MIMap.miKer {Θ : Desc D u} (h : MIMap D u Θ) : MIKer D u Θ := by
  obtain ⟨s, l, FF, hl, hi, h⟩ := h
  refine ⟨FF, hi, fun φ h0 F => ?_⟩
  have h1 := h φ F
  rw [h0, LinearMap.zero_apply, mul_zero] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left hl

theorem OntoAll.ontoP {Θ : Desc D u} (h : OntoAll D u Θ) : OntoP D u Θ := by
  intro x hx
  obtain ⟨F, hF⟩ := h (D.s.Pu u x)
  have h1 := hx F
  rw [hF] at h1
  exact inner_self_eq_zero.1 h1

theorem kerIncl_of {Θ : Desc D u} (h : MIKer D u Θ) (h' : OntoP D u Θ) : KerIncl D u := by
  obtain ⟨FF, hi, h⟩ := h
  exact ⟨FF, hi, fun φ h0 => h' _ (h φ h0)⟩

theorem d0_eq : d0 D u = D.duS u := (D.s_Cu u).finrank_eq

example (FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u) (h : Function.Injective FF) : MIMap D u 0 :=
  ⟨0, 1, FF, one_ne_zero, h, fun _ _ => by simp⟩

example (h : OntoAll D u 0) (y : D.s.HH) : y = 0 := by
  obtain ⟨F, hF⟩ := h y
  simpa using hF.symm

end GlobalTheory.Core.Rk

end
