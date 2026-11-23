import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveTensorOfFibreProjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_tensor_of_fibre_projective' : ∀ (C k B : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Field k] [CommRing B] (σ : C →+* k), Function.Surjective σ → ∀ (H V : Type 1) [AddCommGroup H] [Module C H] [AddCommGroup V] [Module k V] (ρ : B →+* Module.End C H) (ρ' : B →+* Module.End k V) (f : H →ₛₗ[σ] V), Module.Finite C H → Module.Projective C H → Function.Surjective f → (∀ h, f h = 0 → h ∈ RingHom.ker σ • (⊤ : Submodule C H)) → (∀ x h, f (ρ x h) = ρ' x (f h)) → (letI := GlobalTheory.HTSummand.tensorModOf ρ'; Module.Projective (k ⊗[ℤ] B) V) → letI := GlobalTheory.HTSummand.tensorModOf ρ; Module.Projective (C ⊗[ℤ] B) H := by
  first | exact @GlobalTheory.HTSummand.projective_tensor_of_fibre_projective | exact GlobalTheory.HTSummand.projective_tensor_of_fibre_projective | (intros; apply GlobalTheory.HTSummand.projective_tensor_of_fibre_projective <;> assumption)
