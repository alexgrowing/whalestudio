import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAugmentationSubspaceTopEqKerSmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterAugmentationSubspace_top_eq_ker_smul : ∀ (k : Type) [Field k] (C : Type) [CommRing C] (H : Type u) [AddCommGroup H] [Module k H] (σ : C →+* Module.End k H) (χ : C →+* k), letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; ∀ x : H, x ∈ GlobalTheory.HTRho.mSub σ χ ⊤ ↔ x ∈ (RingHom.ker (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) • ⊤ : Submodule (k ⊗[ℤ] C) H) := by
  first | (exact @GlobalTheory.HTRho.mSub_top_eq_ker_smul) | (exact GlobalTheory.HTRho.mSub_top_eq_ker_smul) | (intros; apply GlobalTheory.HTRho.mSub_top_eq_ker_smul  <;> assumption)
