import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_homLattice_iff_integralMatrix_splitChart : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (S T : HSp D) (βS : GL (Fin S.rank) (Fv D.host.F v)) (βT : GL (Fin T.rank) (Fv D.host.F v)), Frame S e π βS → Frame T e π βT → ∃ c : Fv D.host.F v, c ≠ 0 ∧ ∀ u : WO S T, IsHalf e u → (u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ↔ IntM (Ov D v) (c • ((βT⁻¹).1 * Matrix.map u π * βS.1))) := by
  first | exact @GlobalTheory.SplitHomLattice.mem_latO_iff_intM | exact GlobalTheory.SplitHomLattice.mem_latO_iff_intM | (intros; apply GlobalTheory.SplitHomLattice.mem_latO_iff_intM <;> assumption)
