import Mathlib

open MvPolynomial

namespace PI

namespace WickFormula

noncomputable def ordEval {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA] {r s : ℕ}
    (a : Fin r → AA) (a' : Fin s → AA) (P : MvPolynomial (Fin r ⊕ Fin s) k) : AA :=
  ∑ m ∈ P.support, P.coeff m • ((List.ofFn fun i => a i ^ m (Sum.inl i)).prod *
    (List.ofFn fun j => a' j ^ m (Sum.inr j)).prod)

noncomputable def delta {k : Type} [CommRing k] {r s : ℕ} (κ : Fin r → Fin s → k) :
    MvPolynomial (Fin r ⊕ Fin s) k →ₗ[k] MvPolynomial (Fin r ⊕ Fin s) k :=
  ∑ i, ∑ j, κ i j • ((pderiv (Sum.inl i)).toLinearMap ∘ₗ (pderiv (Sum.inr j)).toLinearMap)

end WickFormula

open WickFormula in

def WickFormula : Prop :=
  ∀ (k AA M : Type) [CommRing k] [Algebra ℚ k] [Ring AA] [Algebra k AA] [AddCommGroup M]
    [Module AA M] (r s : ℕ) (a b : Fin r → AA) (a' b' : Fin s → AA) (κ : Fin r → Fin s → k)
    (σ₀ : M),
    (∀ i i', Commute (a i) (a i') ∧ Commute (a i) (b i') ∧ Commute (b i) (b i')) →
    (∀ j j', Commute (a' j) (a' j') ∧ Commute (a' j) (b' j') ∧ Commute (b' j) (b' j')) →
    (∀ i j, Commute (b i) (b' j)) →
    (∀ i j, b i * a' j - a' j * b i = algebraMap k AA (κ i j)) →
    (∀ i, b i • σ₀ = 0) → (∀ j, b' j • σ₀ = 0) →
    ∀ P : MvPolynomial (Fin r ⊕ Fin s) k,
      ordEval (a + b) (a' + b') P • σ₀ =
        ∑ n ∈ Finset.range (P.totalDegree + 1),
          ordEval a a' ((n.factorial : ℚ)⁻¹ • (delta κ ^ n) P) • σ₀

end PI
