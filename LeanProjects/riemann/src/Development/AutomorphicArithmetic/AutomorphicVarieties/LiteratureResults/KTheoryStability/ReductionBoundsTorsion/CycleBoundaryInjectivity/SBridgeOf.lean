import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.ThEqZeroIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.ICyclesInjective

noncomputable section

open UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

open NaturalTheta in
theorem sBridge_of : SBridge := by
  intro k
  have h0 : ∀ (G : Type) [Group G] (m : ℕ),
      bd G m ∘ₗ (eC G (m + 1)).toLinearMap = (eC G m).toLinearMap ∘ₗ (Dz G m).baseChange ℝ :=
    fun G _ m => by rw [Dz_eq_bdZ]; exact bd_eC G m
  refine ⟨fun G _ => th (Dz G k) (pz G k) (eC G (k + 1)) (eC G k) (bd G k) (h0 G k), ?_, ?_, ?_⟩
  · intro G _
    exact th_surjective _ _ _ _ _ (pz_surjective G k) _
  · intro G _ z
    exact th_eq_zero_iff (Dz G (k + 1)) (Dz G k) (pz G k) (eC G (k + 2)) (eC G (k + 1)) (eC G k)
      (bd G (k + 1)) (bd G k) (Dz_Dz G k) (pz_eq_zero_iff G k) (pz_surjective G k) (h0 G (k + 1))
      (h0 G k) z
  · intro G H _ _ f z z' hz
    exact th_natural _ _ _ _ _ _ _ _ _ _ (h0 G k) (h0 H k) _ _ _ (cmap_eC G f (k + 1))
      (map_mem_ker k f) (pz_natural k f) z z' hz

end PositivityTheory.KB
