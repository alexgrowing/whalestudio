import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.FirstSubSecondLeviFamily

noncomputable section

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

def ThetaSelf : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPair E1 E2 →
    (∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x) →
    (∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x) → Nontrivial V →
    (∀ v w : V, v ≠ 0 → ∃ x ∈ alg E1 E2, x v = w) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ y ∈ S, kF E1 E2 a b y ∈ S) →
      ∃ T : V ≃ₗ[ℂ] V, ∀ a b, T.toLinearMap * E1 a b = E2 a b * T.toLinearMap ∧
        T.toLinearMap * E2 a b = E1 a b * T.toLinearMap

def ThetaSelfH : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V), IsPair E1 E2 →
    (∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x) →
    (∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x) → Nontrivial V →
    (∀ v w : V, v ≠ 0 → ∃ x ∈ alg E1 E2, x v = w) →
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ y ∈ S, kF E1 E2 a b y ∈ S) →
    (∃ μ ∈ harmSet lam, hwSp E1 E2 μ ≠ ⊥) →
      ∃ T : V ≃ₗ[ℂ] V, ∀ a b, T.toLinearMap * E1 a b = E2 a b * T.toLinearMap ∧
        T.toLinearMap * E2 a b = E1 a b * T.toLinearMap

end PositivityTheory.RgBcC.RealD
