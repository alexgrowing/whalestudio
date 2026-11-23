import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlIntegralInvMulOfLatticeMapEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glIntegral_inv_mul_of_lattice_map_eq : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) (h h' : GL (Fin r) K), (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → GlobalTheory.SplitHecke.GInt O (h⁻¹ * h') := by
  first | exact @GlobalTheory.SplitHecke.gInt_inv_mul_of_map_eq | exact GlobalTheory.SplitHecke.gInt_inv_mul_of_map_eq | (intros; apply GlobalTheory.SplitHecke.gInt_inv_mul_of_map_eq <;> assumption)
