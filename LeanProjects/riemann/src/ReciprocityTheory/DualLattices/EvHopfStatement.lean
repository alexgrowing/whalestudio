import ReciprocityTheory.DualLattices.TowerZeroSurjective

noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvHopfStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], Function.Injective (algebraMap (Tw.O : Type) C) →
    (∀ f ∈ D.evImg C, addPull (Tw.O : Type) (Nb p g) f ∈ tensorSpan (Tw.O : Type) (D.evImg C)) ∧
      ∀ f ∈ D.evImg C, (fun x => f (-x)) ∈ D.evImg C

end ReciprocityTheory.PGsh.Be2
