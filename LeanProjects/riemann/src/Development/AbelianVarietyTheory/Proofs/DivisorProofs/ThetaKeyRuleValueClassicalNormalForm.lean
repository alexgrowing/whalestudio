import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KeyFormulaIffClauses

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem key_value_of_nf : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) → Mx.det ≠ 0 ∧ (κ ℂ x : ℂ) * c ^ 8 = Mx.det ^ 4 := by
  intro κ hH hT g x hg u τ a b c Mx h
  subst hg
  obtain ⟨h₁, h₂, ha, hb, hc, hΛ, hr, hs, hd⟩ := h
  have hW := GlobalTheory.KeyFormulaCompare.det_ne_zero x u ((2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx) hd
  have hM : Mx.det ≠ 0 := by
    rw [Matrix.det_smul] at hW
    exact right_ne_zero_of_mul hW
  refine ⟨hM, ?_⟩
  have hN : KeyPow.NormalAt x τ Mx a b c := ⟨u, h₁, h₂, hΛ, hr, hs, hd⟩
  obtain ⟨P, hg, rig, hr', th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, h₀, e₁, e₂⟩ := KeyConst.exists_rescale _ _ _ _ _ _ _ _ _ _ _ _ _ hc hM hN
  obtain ⟨u₀, t₁, t₂, t₃, t₄, t₅, t₆⟩ := (KeyPow.normalAt_one_iff _ _ _ _).1 h₀
  have h₃ := hH ℂ P hg rig hr' th₀ hth₀ v₀ hv₀ th hth v hv c Mx e₁ e₂
  have h₄ := hT _ u₀ _ _ _ t₁ t₂ ha hb t₃ t₄ t₅ t₆
  rw [h₄, Units.val_one, _root_.mul_one] at h₃
  rw [mul_comm]
  exact h₃.trans (_root_.mul_one _)

end GlobalTheory.MBLow.Cl
