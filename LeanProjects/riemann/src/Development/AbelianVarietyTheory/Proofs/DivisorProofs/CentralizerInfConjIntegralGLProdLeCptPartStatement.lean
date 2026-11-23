import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerInfConjIntegralGLProdLeCptPart
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_inf_conj_integralGLProd_le_cptPart : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E) (m q : GLw a w × GLw b w), twCent (MonoidHom.id _) m ⊓ ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)).map (MulAut.conj q).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) m) := by
  first | exact @GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart | exact GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart | (intros; apply GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart <;> assumption)
