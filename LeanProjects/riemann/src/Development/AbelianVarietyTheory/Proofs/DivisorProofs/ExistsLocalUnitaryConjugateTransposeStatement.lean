import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitaryConjugateTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_unitary_conjugate_transpose : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Unr E → SelfDualLat G Λ → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ h : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E), Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv (maximalRealSubfield E) v) (cj E)) (h : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) * JR (F := maximalRealSubfield E) (Fv (maximalRealSubfield E) v) Gᵀ * (h : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) = 1 ∧ ∀ z : Fin r → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E, z ∈ latLoc (maximalRealSubfield E) Λ v ↔ ∀ i, (((h⁻¹ : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) *ᵥ z) i ∈ intLoc (maximalRealSubfield E) E v := by
  first | exact @GlobalTheory.TamOne.exists_orthonormal_frame_latLoc | exact GlobalTheory.TamOne.exists_orthonormal_frame_latLoc | (intros; apply GlobalTheory.TamOne.exists_orthonormal_frame_latLoc <;> assumption)
