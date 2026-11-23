import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitaryGroup_iso : ∀ {D : D7} (V V' : HSp D) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (j' : Matrix (Fin V.rank) (Fin V'.rank) (EAf D)), HMul.hMul j j' = 1 → HMul.hMul j' j = 1 → HMul.hMul (HMul.hMul (Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) j) (V'.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))) j = V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) → ∃ Φ : GfC V ≃ₜ* GfC V', ∀ g : GfC V, HMul.hMul (finE V' (Φ g : GA D V')).val j = HMul.hMul j (finE V (g : GA D V)).val := by
  first | exact @GlobalTheory.FinIsoGrp.exists_finIso | exact GlobalTheory.FinIsoGrp.exists_finIso | (intros; apply GlobalTheory.FinIsoGrp.exists_finIso <;> assumption)
