import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeHeightComapFiniteType
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.AlgStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_le_height_comap_finite_type : ∀ (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] [Algebra.FiniteType R S] [Algebra.IsAlgebraic R S] (q : Ideal S) [q.IsPrime], q.height ≤ (q.comap (algebraMap R S)).height := by
  first | exact @GlobalTheory.HeightContract.height_le_height_comap | exact GlobalTheory.HeightContract.height_le_height_comap | (intros; apply GlobalTheory.HeightContract.height_le_height_comap <;> assumption)
