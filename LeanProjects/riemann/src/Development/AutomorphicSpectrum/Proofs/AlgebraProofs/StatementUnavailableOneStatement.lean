import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StatementUnavailableOne
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.statement_unavailable_one : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (emb : (E →+* C) → (𝓞 E →+* V)), (∀ s (a : 𝓞 E), algebraMap V C (emb s a) = s (a : E)) → Nat.card (E →+* C) = Module.finrank ℚ E → ∀ σ : E →+* C, ∃ π : 𝓞 E, (∀ s s' : E →+* C, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → (∀ a, ¬ IsUnit (emb s' a - emb σ a)) → emb s π = emb s' π → s = s') ∧ ∀ f : (E →+* C) → V, (∀ s, (∃ a, IsUnit (emb s a - emb σ a)) → f s = 0) → ((∃ g : Polynomial V, ∀ s, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.block_monogenic_of_residual_character | exact GlobalTheory.CompanionTheory.Ar.Flat.block_monogenic_of_residual_character | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.block_monogenic_of_residual_character <;> assumption)
