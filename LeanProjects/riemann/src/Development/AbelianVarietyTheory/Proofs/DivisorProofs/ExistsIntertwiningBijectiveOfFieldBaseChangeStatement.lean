import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntertwiningBijectiveOfFieldBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange : ∀ (K F : Type) [Field K] [Field F] [Algebra K F] [Infinite K] (V W V' W' : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W'] [FiniteDimensional F V'] (iV : V →ₛₗ[algebraMap K F] V') (iW : W →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension iV → GlobalTheory.FieldBaseChange.IsExtension iW → ∀ (J : Type) (a : J → V →ₗ[K] V) (b : J → W →ₗ[K] W) (a' : J → V' →ₗ[F] V') (b' : J → W' →ₗ[F] W'), (∀ i v, a' i (iV v) = iV (a i v)) → (∀ i w, b' i (iW w) = iW (b i w)) → ∀ E' : V' →ₗ[F] W', Function.Bijective E' → (∀ i v, E' (a' i v) = b' i (E' v)) → ∃ E : V →ₗ[K] W, Function.Bijective E ∧ ∀ i v, E (a i v) = b i (E v) := by
  first | exact @GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | exact GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | (intros; apply GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension <;> assumption)
