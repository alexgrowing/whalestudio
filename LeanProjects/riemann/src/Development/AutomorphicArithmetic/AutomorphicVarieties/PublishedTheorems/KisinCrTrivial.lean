import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology

noncomputable section

namespace UpperTheory.V.Published

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc IsLocalRing

def KisinCrFull : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (A₀ : Type) [CommRing A₀] [IsLocalRing A₀] [IsNoetherianRing A₀] [IsAdicComplete (maximalIdeal A₀) A₀]
    [Finite (ResidueField A₀)] [CharP (ResidueField A₀) l] [Algebra ℤ_[l] A₀]
    (A : Type) [CommRing A] [Algebra A₀ A] [IsLocalization.Away ((l : ℕ) : A₀) A] [Algebra E A],
    (∀ z : ℤ_[l], algebraMap E A (algebraMap ℚ_[l] E (z : ℚ_[l])) = algebraMap A₀ A (algebraMap ℤ_[l] A₀ z)) →
    (∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra ℤ_[l] O)
      (_ : Module.Finite ℤ_[l] O) (_ : Algebra O E) (_ : IsFractionRing O E) (_ : Algebra O A₀),
      (∀ z : ℤ_[l], algebraMap ℚ_[l] E (z : ℚ_[l]) = algebraMap O E (algebraMap ℤ_[l] O z)) ∧
      ∀ a : O, algebraMap E A (algebraMap O E a) = algebraMap A₀ A (algebraMap O A₀ a)) →
  ∀ (n : ℕ) (r : ↥(GK K) →* GL (Fin n) A₀),
    (∀ (N : ℕ) (i j : Fin n), IsLocallyConstant fun g =>
      Ideal.Quotient.mk (maximalIdeal A₀ ^ N) ((r g : Matrix (Fin n) (Fin n) A₀) i j)) →
  ∀ (τ : ↥((Iq l).subgroupOf (GK K)) →* GL (Fin n) E), IsOpen (τ.ker : Set ↥((Iq l).subgroupOf (GK K))) →
  ∀ (t : ↥(GK K) → E), (∀ γ : ↥((Iq l).subgroupOf (GK K)), t γ = (τ γ : Matrix (Fin n) (Fin n) E).trace) →
  ∀ m : ℤ → ℕ, ∃ I : Ideal A,
    ∀ (B : Type) [CommRing B] [Algebra E B] [Module.Finite E B] [Algebra ℚ_[l] B] [IsScalarTower ℚ_[l] E B]
      (x : A →ₐ[E] B), I ≤ RingHom.ker x ↔
        PotCrysType K (colRep ((Matrix.GeneralLinearGroup.map ((x : A →+* B).comp (algebraMap A₀ A))).comp r)) n m
          fun γ => algebraMap E B (t γ)

end UpperTheory.V.Published
