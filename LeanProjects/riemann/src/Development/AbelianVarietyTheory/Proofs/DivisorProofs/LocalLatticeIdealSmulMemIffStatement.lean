import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIdealSmulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_ideal_smul_mem_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (𝔞 : Ideal (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin n) (Fv F v ⊗[F] E)), (∀ z : Fin n → Fv F v ⊗[F] E, z ∈ latLoc F L v ↔ ∀ i, (((h⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ z) i ∈ intLoc F E v) → ∀ z : Fin n → Fv F v ⊗[F] E, z ∈ latLoc F (𝔞 • L) v ↔ ∀ i, ∃ t ∈ 𝔞.map (intLocIncl (E := E) v), ((t : intLoc F E v) : Fv F v ⊗[F] E) = (((h⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ z) i := by
  first | exact @GlobalTheory.TamOne.IdealLoc.latLoc_smul_iff_of_frame | exact GlobalTheory.TamOne.IdealLoc.latLoc_smul_iff_of_frame | (intros; apply GlobalTheory.TamOne.IdealLoc.latLoc_smul_iff_of_frame <;> assumption)
