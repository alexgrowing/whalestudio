import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsZsmulMemLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingleMemLatLoc

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.AdelicU

theorem exists_zsmul_mem_of_isLattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (x : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice
  | exact _root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice
  | (apply _root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeIntegerMultiple.exists_zsmul_mem_lattice ..)

theorem exists_single_mem_latLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ c : Fv F v, c ≠ 0 ∧
      ∀ i : Fin n, (Pi.single i (c ⊗ₜ[F] (1 : E)) : Fin n → Fv F v ⊗[F] E) ∈ latLoc F L v := by
  first
  | exact @_root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc
  | exact _root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc
  | (apply _root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalLatticeIntegral.exists_single_mem_latLoc ..)

end GlobalTheory.AdelicU
