import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open TensorProduct GlobalTheory.PDivGroup

def HodgeTateCokerSharp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [Algebra ℤ_[p] O], v.Integers O → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : O)}) O → ∀ G : PDivGroup p O,
    ∀ κ : O, v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C) →
      ∀ w : G.dual.omega, κ • w ∈ LinearMap.range (hodgeTateLinear G)

end GlobalTheory.CompanionTheory.Ar.HT
