import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData

set_option autoImplicit false

noncomputable section

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramePairGram

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def ent (M : Matrix (Fin r) (Fin r) ℂ) (a b : ℕ) : ℂ := if h : a < r ∧ b < r then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

open Classical in

def coef (X : Data E r) (x x' : Frame X.Ψ r) (ρ : E →+* ℂ) (b i : ℕ) : ℂ :=
  if h : ρ ∈ X.Ψ then ent ((mat x' ⟨ρ, h⟩)⁻¹ * mat x ⟨ρ, h⟩) (X.p0 + b) (X.p0 + i)
  else if h' : conjEmb ρ ∈ X.Ψ then ent ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) (X.p0 - 1 - i) (X.p0 - 1 - b)
  else 0

example (X : Data E r) (x : Frame X.Ψ r) (hx : x ∈ X.dom) (ρ : X.Ψ) (b i : ℕ) (hb : X.p0 + b < r) (hi : X.p0 + i < r) :
    coef X x x ρ.1 b i = if b = i then 1 else 0 := by
  have hd : IsUnit (mat x ρ).det := (hx ρ).1.isUnit
  simp only [coef, dif_pos ρ.2, ent, dif_pos (And.intro hb hi), Subtype.coe_eta, nonsing_inv_mul _ hd, one_apply,
    Fin.mk.injEq, Nat.add_left_cancel_iff]

end GlobalTheory.FramePairGram
