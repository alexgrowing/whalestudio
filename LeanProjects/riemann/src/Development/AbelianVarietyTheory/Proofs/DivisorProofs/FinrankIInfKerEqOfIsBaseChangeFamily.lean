import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIInfKerOfIsBaseChange

open Module

namespace GlobalTheory.BadCount

theorem finrank_iInf_ker_baseChange : ∀ (K L V W ι : Type) [Field K] [Field L] [Algebra K L]
    [Finite ι] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f →
    ∀ (a : ι → V →ₗ[K] V) (a' : ι → W →ₗ[L] W), (∀ i v, a' i (f v) = f (a i v)) →
      finrank L (⨅ i, LinearMap.ker (a' i) : Submodule L W) =
          finrank K (⨅ i, LinearMap.ker (a i) : Submodule K V) ∧
        (⨅ i, LinearMap.ker (a' i) : Submodule L W) =
          Submodule.span L (f '' ((⨅ i, LinearMap.ker (a i) : Submodule K V) : Set V)) := by
  intro K L V W ι _ _ _ _ _ _ _ _ _ _ _ f hf a a' ha
  refine ⟨GlobalTheory.finrank_iInf_ker_of_isBaseChange K L V W ι f a a' hf ha, ?_⟩
  rw [GlobalTheory.GaloisDescent.span_image_iInf hf]
  exact iInf_congr fun i =>
    (GlobalTheory.GaloisDescent.span_image_ker hf hf (a i) (a' i) (fun v => ha i v)).symm

end GlobalTheory.BadCount
