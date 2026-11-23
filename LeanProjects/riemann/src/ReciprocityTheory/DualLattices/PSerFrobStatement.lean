import ReciprocityTheory.DualLattices.TowerZeroSurjective

noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def nsmulF {S : Type} [CommRing S] [Algebra R₀ S] (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀)
    (a : Fin g → S) : ℕ → Fin g → S
  | 0 => 0
  | n + 1 => fAdd F (nsmulF F a n) a

def PSerFrobStatement (p : ℕ) [Fact p.Prime] (K : LAlg R₀) (ch : FormalChartAtZero B K g) : Prop :=
  ∀ N : ℕ, ∃ G : Fin g → MvPolynomial (Fin g) R₀,
    (∀ k m, (∃ i, ¬ p ∣ m i) → ∃ r : R₀, MvPolynomial.coeff m (G k) = p * r) ∧
    ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, a i ^ N = 0) →
      nsmulF ch.F a p = fun k => MvPolynomial.aeval a (G k)

end ReciprocityTheory.PGsh.Be2
