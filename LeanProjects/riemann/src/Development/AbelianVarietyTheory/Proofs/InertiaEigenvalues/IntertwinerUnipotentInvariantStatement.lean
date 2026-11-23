import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_unipotent_invariant : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (n : ℕ) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Gn g n) W) (ρ' : Representation ℂ (Gn g n) W') (T : W →ₗ[ℂ] W') (a : Fin n → ℤ) (f f' : (ZMod g)[X]), (∀ u : Gn g n, (∀ i j, ¬ a i < a j → (u : Mt g n) i j = (1 : Mt g n) i j) → T ∘ₗ ρ u = T) → (∀ u : Gn g n, (∀ i j, ¬ a j < a i → (u : Mt g n) i j = (1 : Mt g n) i j) → ρ' u ∘ₗ T = T) → (∀ m : Gn g n, (∀ i j, a i ≠ a j → (m : Mt g n) i j = 0) → T ∘ₗ ρ m = ρ' m ∘ₗ T) → (∀ w, ρ.asAlgebraHom (eSerC L n f) w = w) → (∀ w', ρ'.asAlgebraHom (eSerC L n f') w' = w') → T ≠ 0 → f = f' := by
  first | exact @GlobalTheory.GLq.Opp.label_eq_of_opposite | exact GlobalTheory.GLq.Opp.label_eq_of_opposite | (intros; apply GlobalTheory.GLq.Opp.label_eq_of_opposite <;> assumption)
