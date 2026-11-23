import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarOnBesselSubgroupProdMap
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHaarOn_besselSubgroup_prod_map : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (UWset k r z) μW → IsHaarOn (Nset k r) μN → IsHaarOn (Sset k r z) ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
  first | exact @GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map | exact GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map | (intros; apply GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map <;> assumption)
