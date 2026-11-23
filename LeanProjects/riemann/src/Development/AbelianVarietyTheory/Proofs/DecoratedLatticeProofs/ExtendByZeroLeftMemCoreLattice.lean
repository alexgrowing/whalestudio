import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMapsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrComb

theorem extL_mem_latO : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S) (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) → ∀ u ∈ latO A S (LA : Set _) (LS : Set _) P, (o.resS S).symm (u, 0) ∈ latO V₀ S (M : Set _) (LS : Set _) P := by
  intro D V₀ A L S o P LA LS M hA hS hM hO u hu
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D A S LA LS hA hS P u] at hu
  obtain ⟨huP, huL⟩ := hu
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D V₀ S M LS hM hS P, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  have hloc := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (huP i k)
  · have hy' := ((hloc V₀).2.2.2 M y hM.1).1 hy
    have hp : o.pA *ᵥ y ∈ latV A LA P := by
      refine ((hloc A).2.2.2 LA (o.pA *ᵥ y) hA.1).2 ⟨fun i => ?_, fun v hv e he => ?_⟩
      · rw [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy'.1 k)
      · obtain ⟨LL, hLL⟩ := hO v hv
        have h1 := ((hLL (e • y)).1 (hy'.2 v hv e he)).1
        rwa [Matrix.mulVec_smul] at h1
    have h2 := huL _ hp
    change (u * o.pA) *ᵥ y ∈ latA S LS P
    rwa [← Matrix.mulVec_mulVec]

end GlobalTheory.ContrComb
