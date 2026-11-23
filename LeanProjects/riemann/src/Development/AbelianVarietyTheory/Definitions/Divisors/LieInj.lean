import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule

noncomputable section

open Matrix GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.DetInv

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] [Algebra ℤ_[p] C] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O C] [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} {h : ℕ}
  {Γ : Type} [CommRing Γ] [Algebra ℤ_[p] Γ]

structure IsTie (P : Point p v O Λ) (D : Datum ε h Γ) (j : Λ →+* Γ)
    (φ : P.V ≃ₗ[C] (Fin h → C)) : Prop where
  lat : ∀ x, x ∈ P.latT ↔ ∀ i, φ x i ∈ (algebraMap O C).range
  act : ∀ a x, φ (P.actV a x) = (actT D (j a)).map (algebraMap O C) *ᵥ φ x
  lie : ∀ x, x ∈ P.latLie ↔ φ x ∈ D.Lie.map (incl C h)
  lieInj : Function.Injective P.bLie
  ker : ∀ x, x ∈ P.W ↔ alC C D (φ x) = 0
  fil : ∀ x, (∀ i, alC C D (φ x) i ∈ (algebraMap O C).range) ↔
    ∀ y ∈ P.latLie, P.pairV y x ∈ (algebraMap O C).range

end GlobalTheory.DetInv
