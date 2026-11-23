import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingleMemLocalLatticeCompletion
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_single_mem_localLatticeCompletion : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∃ c : Fv F v, c ≠ 0 ∧ ∀ i : Fin n, (Pi.single i (c ⊗ₜ[F] (1 : E)) : Fin n → Fv F v ⊗[F] E) ∈ latLoc F L v := by
  first | exact @GlobalTheory.AdelicU.exists_single_mem_latLoc | exact GlobalTheory.AdelicU.exists_single_mem_latLoc | (intros; apply GlobalTheory.AdelicU.exists_single_mem_latLoc <;> assumption)
