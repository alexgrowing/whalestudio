import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.WickFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.GenDefs

open MvPolynomial

namespace PI.WickFormula

theorem delta_eq_gdelta {k : Type} [CommRing k] {r s : ℕ} (κ : Fin r → Fin s → k) : delta κ = Gen.gdelta κ := rfl

structure Hyp {k AA M : Type} [CommRing k] [Ring AA] [Algebra k AA] [AddCommGroup M] [Module AA M] {r s : ℕ}
    (a b : Fin r → AA) (a' b' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M) : Prop where
  h1 : ∀ i i', Commute (a i) (a i') ∧ Commute (a i) (b i') ∧ Commute (b i) (b i')
  h2 : ∀ j j', Commute (a' j) (a' j') ∧ Commute (a' j) (b' j') ∧ Commute (b' j) (b' j')
  h3 : ∀ i j, Commute (b i) (b' j)
  h4 : ∀ i j, b i * a' j - a' j * b i = algebraMap k AA (κ i j)
  h5 : ∀ i, b i • σ₀ = 0
  h6 : ∀ j, b' j • σ₀ = 0

def OrdLin : Prop :=
  ∀ (k AA : Type) [CommRing k] [Ring AA] [Algebra k AA] (r s : ℕ) (a : Fin r → AA) (a' : Fin s → AA),
    ∃ f : MvPolynomial (Fin r ⊕ Fin s) k →ₗ[k] AA, ∀ P, f P = ordEval a a' P

def OrdX : Prop :=
  ∀ (k AA : Type) [CommRing k] [Ring AA] [Algebra k AA] (r s : ℕ) (a : Fin r → AA) (a' : Fin s → AA),
    (∀ i i', Commute (a i) (a i')) →
    ∀ (i : Fin r) (R : MvPolynomial (Fin r ⊕ Fin s) k), ordEval a a' (X (Sum.inl i) * R) = a i * ordEval a a' R

def Base : Prop :=
  ∀ (k AA M : Type) [CommRing k] [Ring AA] [Algebra k AA] [AddCommGroup M] [Module AA M] (r s : ℕ)
    (a b : Fin r → AA) (a' b' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M), Hyp a b a' b' κ σ₀ →
    ∀ Q : MvPolynomial (Fin r ⊕ Fin s) k, (∀ m ∈ Q.support, ∀ i, m (Sum.inl i) = 0) →
      ordEval (a + b) (a' + b') Q • σ₀ = ordEval a a' Q • σ₀

def BComm : Prop :=
  ∀ (k AA M : Type) [CommRing k] [Ring AA] [Algebra k AA] [AddCommGroup M] [Module AA M] (r s : ℕ)
    (a b : Fin r → AA) (a' b' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M), Hyp a b a' b' κ σ₀ →
    ∀ (i : Fin r) (R : MvPolynomial (Fin r ⊕ Fin s) k),
      b i • (ordEval (a + b) (a' + b') R • σ₀) = ordEval (a + b) (a' + b') (Gen.dL κ i R) • σ₀

end PI.WickFormula
