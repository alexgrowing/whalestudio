import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normAt_sq_integralForm_eq_classSumMetric : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V), ((Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x ^ 2 : ℝ) : ℂ) = cSum I hX a (toCx I hX a x) (toCx I hX a x) := by
  first | exact @GlobalTheory.Mem.Df.normAt_sq_eq_cSum | exact GlobalTheory.Mem.Df.normAt_sq_eq_cSum | (intros; apply GlobalTheory.Mem.Df.normAt_sq_eq_cSum <;> assumption)
