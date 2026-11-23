import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimpLabMinValOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Mult

variable {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]

def cellMult {m : ℕ} (δ : Fin m → balForms bar X) : ℕ :=
  Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ Submodule.span ℤ (Set.range δ)))

def IsPrim (β : balForms bar X) : Prop :=
  ∀ (k : ℕ) (β' : balForms bar X), β = k • β' → k = 1

def maxMult (q : ℕ) (φ : InvFun O) : ℕ∞ :=
  ⨆ (X : Type) (_ : AddCommGroup X) (_ : Module O X) (_ : Module.Finite O X) (_ : Module.Projective O X)
    (_ : Module.finrank O X ≤ q) (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ)
    (_ : LinearIndependent ℤ δ) (_ : ∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)),
    ((cellMult bar fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) : ℕ∞)

variable {bar}

theorem not_isPrim_zero : ¬ IsPrim bar (0 : balForms bar X) := fun h => by
  have := h 0 0 (by simp)
  exact zero_ne_one this

end Mult

end GlobalTheory.PolFan
