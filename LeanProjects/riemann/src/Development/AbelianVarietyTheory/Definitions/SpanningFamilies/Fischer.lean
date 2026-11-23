import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

open Matrix Complex NumberField MeasureTheory
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.SW

namespace GlobalTheory.Ker

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) {n : ℕ}

abbrev WR (X : Data E r) (n : ℕ) : Type := X.Ψ → Fin n → Fin r → ℂ

def embR (y : Matrix (Fin n) (Fin r) E) : WR X n := fun τ k a => τ.1 (y k a)

def zR (x : Frame X.Ψ r) (v : WR X n) : Fin n → Fin g → ℂ := fun k i =>
  if ((idx i).2 : ℕ) < X.p0 then
    hermC (idx i).1.1 X.Gm (FD.col (mat x (idx i).1) (idx i).2) (v (idx i).1 k)
  else ((mat x (idx i).1)⁻¹ *ᵥ v (idx i).1 k) (idx i).2

def EFR (v v' : WR X n) : ℝ :=
  ∑ τ : X.Ψ, ∑ k, 2 * (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (v τ k) (v' τ k)).re

def gaussR (x : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) : ℂ :=
  cexp (-(Real.pi / 2 * ∑ k, GlobalTheory.Dict.hx X bas idx x (z k) (z k)))

def thR (φ : TF n g) (x : Frame X.Ψ r) (v : WR X n) : ℂ :=
  gaussR X bas idx x (zR X idx x v) * thA X bas idx φ x (zR X idx x v)

def latR (n N : ℕ) : AddSubgroup (WR X n) :=
  AddSubgroup.closure {v | ∃ y : Matrix (Fin n) (Fin r) E, (∀ k, y k ∈ X.Λ) ∧ v = N • embR X y}

def IsONFr (x : Frame X.Ψ r) : Prop := ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X

def IdemTwo (w : E) : Prop := ∃ b : E, IsIntegral ℤ b ∧ w * cc w = 2 * b

def fischer {σ : Type} (P Q : MvPolynomial σ ℂ) : ℂ :=
  ∑ m ∈ P.support, ((m.prod fun _ e => e.factorial : ℕ) : ℂ) * (P.coeff m * conj (Q.coeff m))

theorem zR_embR (x : Frame X.Ψ r) (y : Matrix (Fin n) (Fin r) E) (k : Fin n) :
    zR X idx x (embR X y) k = GlobalTheory.Dict.pv X idx x (y k) := rfl

end

end GlobalTheory.Ker
