import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab

noncomputable section

namespace GlobalTheory.MirAvg

open Polynomial GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

def mirSet {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h : Gn g r) : Prop :=
  if b then ∀ x : Fin r → ZMod g, ∃ c : ZMod g, (h : Mt g r).mulVec x - x = c • a
  else ∀ x : Fin r → ZMod g, a ⬝ᵥ x = 0 → (h : Mt g r).mulVec x = x

open Classical in

def mirEl {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) : MonoidAlgebra ℂ (Gn g r) :=
  ∑ h : Gn g r, MonoidAlgebra.single h (if mirSet a b h then ((θ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) else 0)

def SeriesKillsAvg : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (r : ℕ) (f : (ZMod g)[X]) (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g),
    GlobalTheory.GLp.IsCharLab L θ c → ¬ f.IsRoot c → ¬ f.IsRoot c⁻¹ → ∀ (a : Fin r → ZMod g) (b : Bool), a ≠ 0 →
      eSerC L r f * mirEl θ a b = 0

end GlobalTheory.MirAvg
