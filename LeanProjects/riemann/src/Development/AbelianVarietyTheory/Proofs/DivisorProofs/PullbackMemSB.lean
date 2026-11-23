import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.FinPull

theorem pullback_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F),
      (fun w : ι → FiniteAdeleRing (𝓞 F) F => g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ w)) ∈
        SB (ι → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ ι κ _ _ D hD g hg
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  set A := algebraMap F (FiniteAdeleRing (𝓞 F) F)
  have hinj : Function.Injective (Matrix.toLin' D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    exact hD z (by simpa using hz)
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' D) (LinearMap.ker_eq_bot.mpr hinj)
  set L := LinearMap.toMatrix' G
  have hLD : L * D = 1 := by
    have : LinearMap.toMatrix' (G ∘ₗ Matrix.toLin' D) = LinearMap.toMatrix' LinearMap.id := by rw [hG]
    simpa [L, LinearMap.toMatrix'_comp] using this
  have hM : Continuous fun w : ι → FiniteAdeleRing (𝓞 F) F => D.map A *ᵥ w :=
    continuous_const.matrix_mulVec continuous_id
  have hN : Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => L.map A *ᵥ w :=
    continuous_const.matrix_mulVec continuous_id
  have hinv : Function.LeftInverse (fun w : κ → FiniteAdeleRing (𝓞 F) F => L.map A *ᵥ w)
      (fun w : ι → FiniteAdeleRing (𝓞 F) F => D.map A *ᵥ w) := fun w => by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hLD, Matrix.map_one A (map_zero A) (map_one A), Matrix.one_mulVec]
  exact ⟨hg.1.comp_continuous hM, hg.2.comp_isClosedEmbedding (hinv.isClosedEmbedding hN hM)⟩

end GlobalTheory.FinPull
