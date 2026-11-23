import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLiftOfSurjKer

set_option autoImplicit false

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace CrystallineSemistableComparison.D

theorem colim_lift : ∀ (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → ∀ (T : Type) [CommRing T] (y : ∀ n, G n →+* T), (∀ n x, y (n + 1) (f n x) = y n x) → ∃ z : L →+* T, ∀ n x, z (ι n x) = y n x := by
  intro A _ G _ _ f L _ _ ι hc T _ y hy
  rcases hc with ⟨h1, h2, h3⟩
  refine GlobalTheory.CompanionTheory.ColimLift.exists_lift_of_surj_ker (fun n => (f n).toRingHom) (fun n => (ι n).toRingHom)
    (fun n k x => tr f n k x) h1 (fun _ _ => rfl) (fun _ _ _ => rfl) h2 (fun n x hx => ?_) y hy
  obtain ⟨k, hk⟩ := h3 n 1 (fun _ => x) (fun _ => hx)
  exact ⟨k, hk 0⟩

end CrystallineSemistableComparison.D
