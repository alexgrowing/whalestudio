import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormMetric_eq_classSumMetric : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (F G : (I.per l u a).Mt) (F' G' : MtCx I a), SameForm I l u a F' F → SameForm I l u a G' G → I.ipMt l u a F G = cSum I hX a F' G' := by
  first | exact @GlobalTheory.Mem.Df.ipMt_eq_cSum | exact GlobalTheory.Mem.Df.ipMt_eq_cSum | (intros; apply GlobalTheory.Mem.Df.ipMt_eq_cSum <;> assumption)
