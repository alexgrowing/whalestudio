import ReciprocityTheory.DualLattices.TowerZeroSurjective

noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def WFrobStatement {K : LAlg R₀} (wd : WData Tw K) (g : ℕ) : Prop :=
  ∀ G : MvPolynomial (Fin g) (wd.W : Type),
    (∀ m, (∃ i, ¬ p ∣ m i) → MvPolynomial.coeff m G ∈ Ideal.span {(p : (wd.W : Type))}) →
    ∃ Q : MvPolynomial (Fin g) (Tw.R 0 : Type), ∀ y : Fin g → (wd.W : Type),
      MvPolynomial.eval y G ∈ Ideal.span {(p : (wd.W : Type))} →
      ∀ a : (wd.W : Type), wd.πW.1 a = MvPolynomial.eval (fun i => wd.πW.1 (y i)) Q →
        MvPolynomial.eval y G = p * a

end ReciprocityTheory.PGsh.Be2
