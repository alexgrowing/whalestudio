import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacteristicPolynomialFreeGenerators
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characteristic_polynomial_free_generators : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [CharZero k] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.charpoly_condition_gives_free_char_zero | exact GlobalTheory.CompanionTheory.Ar.Flat.charpoly_condition_gives_free_char_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.charpoly_condition_gives_free_char_zero <;> assumption)
