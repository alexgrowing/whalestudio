import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteUnramifiedExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_unramified_extension : ∀ (B C : Type) [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C] (ψ : B →+* C), IsNoetherianRing C → IsLocalHom ψ → ψ.Flat → (IsLocalRing.maximalIdeal B).map ψ = IsLocalRing.maximalIdeal C → ((IsLocalRing.residue C).comp ψ).Finite → ((IsLocalRing.residue C).comp ψ).FormallyUnramified → ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ι : C →+* R'), IsNoetherianRing R' ∧ IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧ IsLocalHom ι ∧ Function.Injective ι ∧ GlobalTheory.Toroidal.IsEtaleCompletion (ι.comp ψ) ∧ ((IsLocalRing.residue R').comp (ι.comp ψ)).FormallyUnramified := by
  first | exact @GlobalTheory.CompletionEtale.exists_completion | exact GlobalTheory.CompletionEtale.exists_completion | (intros; apply GlobalTheory.CompletionEtale.exists_completion <;> assumption)
