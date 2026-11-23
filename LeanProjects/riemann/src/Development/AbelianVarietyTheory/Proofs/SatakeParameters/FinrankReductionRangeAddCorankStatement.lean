import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankReductionRangeAddCorank
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_reduction_range_add_corank : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (n j : ℕ) (a : GL (Fin n) K) (A : Matrix (Fin n) (Fin n) O), j ≤ n → Hk O p j a → A.map (algebraMap O K) = a.1 → Module.finrank (IsLocalRing.ResidueField O) (LinearMap.range (A.map (IsLocalRing.residue O)).mulVecLin) + j = n := by
  first | exact @GlobalTheory.SplitHecke.finrank_range_reduction | exact GlobalTheory.SplitHecke.finrank_range_reduction | (intros; apply GlobalTheory.SplitHecke.finrank_range_reduction <;> assumption)
