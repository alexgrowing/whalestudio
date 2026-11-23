import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiFinRat
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
open GlobalTheory.BoxLattice GlobalTheory.EvAdm

namespace GlobalTheory.BoxLattice

theorem exists_ratFin_coset : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ ρ : κ → F, ratFin F κ ρ - r ∈ scaledInt F κ a := by
  intro F _ _ κ _ a _ r
  have hd : DenseRange (Pi.map fun (_ : κ) => algebraMap F (FiniteAdeleRing (𝓞 F) F)) :=
    DenseRange.piMap fun _ => GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F
  have hop : IsOpen {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ scaledInt F κ a} :=
    (isOpen_scaledInt a).preimage (continuous_id.sub continuous_const)
  obtain ⟨ρ, hρ⟩ := hd.exists_mem_open hop ⟨r, by simp [zero_mem]⟩
  exact ⟨ρ, hρ⟩

end GlobalTheory.BoxLattice
