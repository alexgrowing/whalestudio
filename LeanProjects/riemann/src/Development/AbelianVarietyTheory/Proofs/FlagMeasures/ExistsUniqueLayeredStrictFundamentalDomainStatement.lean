import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueLayeredStrictFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_layered_strictFundamentalDomain : ∀ {G X B : Type} [Group G] [Finite B] {V : B → Type} [∀ β, AddCommGroup (V β)] (ρ : G → X → X) (NN : Set X) (o : X) (deg : B → ℕ) (c : ∀ β, X → V β) (L D : ∀ β, Set (V β)), o ∈ NN → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ β, (0 : V β) ∈ L β) → (∀ β v, ∃! l, l ∈ L β ∧ v + l ∈ D β) → (∀ β, c β o = 0) → (∀ (d : ℕ) (g : G), (∀ β, deg β < d → c β (ρ g o) = 0) → ∀ x ∈ NN, ∀ β, deg β ≤ d → c β (ρ g x) = c β x + c β (ρ g o)) → (∀ (g : G) (β : B), (∀ β', deg β' < deg β → c β' (ρ g o) = 0) → c β (ρ g o) ∈ L β) → (∀ β, ∀ l ∈ L β, ∃ g : G, c β (ρ g o) = l ∧ ∀ β', β' ≠ β → deg β' ≤ deg β → c β' (ρ g o) = 0) → (∀ g : G, (∀ β, c β (ρ g o) = 0) → g = 1) → ∀ x ∈ NN, ∃! g : G, ∀ β, c β (ρ g x) ∈ D β := by
  first | exact @GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain | exact GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain | (intros; apply GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain <;> assumption)
