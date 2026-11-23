import Mathlib

namespace Formalism.RankGapBounds.ExistsSmulMemTer

abbrev G0 := ZMod 2 × ZMod 2
abbrev GG (e : ℕ) := G0 × ZMod (2 ^ e)

def sg : G0 := (1, 0)
def c0 : G0 := (0, 1)
def cc (e : ℕ) : GG e := (c0, 0)

def InPhi {e : ℕ} (γ : GG e) : Prop := γ.1.2 = 0

def place {e : ℕ} (γ : GG e) : GG e := if γ.1.2 = 0 then γ else γ + cc e

def OrbitParity : Prop :=
  ∀ (e : ℕ) (φ τ : GG e) (i : ℕ), φ.1.2 = 1 → InPhi τ → (InPhi (i • φ + τ) ↔ Even i)

def OrbitCoord : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)) (i : ℕ), (place (i • φ + ((0 : G0), t))).2 = t + i • φ.2

def OrbitOver : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)) (i : ℕ),
    (φ.1 = c0 → (place (i • φ + ((0 : G0), t))).1 = 0) ∧
    (φ.1 = sg + c0 → (place (i • φ + ((0 : G0), t))).1 = if Even i then 0 else sg)

def ConjInOrbit : Prop :=
  ∀ (e : ℕ) (φ : GG e), φ.1.2 = 1 → (cc e ∈ AddSubgroup.zmultiples φ ↔ φ = cc e)

def OrbitCard : Prop :=
  ∀ (e : ℕ) (φ : GG e) (t : ZMod (2 ^ e)), φ.1 = c0 → φ.2 ≠ 0 →
    (Set.range fun i : ℕ => place (i • φ + ((0 : G0), t))).ncard = addOrderOf φ.2 ∧
    Even (addOrderOf φ.2)

end Formalism.RankGapBounds.ExistsSmulMemTer
