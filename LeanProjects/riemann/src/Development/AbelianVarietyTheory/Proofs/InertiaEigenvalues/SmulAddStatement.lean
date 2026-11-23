import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.repr_smul_add : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (c : k) (z z' : G → Fin A.m → k) (b g b' g' : ZMod n → Vc k A.m), Repr F A z b g → Repr F A z' b' g' → Repr F A (c • z + z') (c • b + b') (c • g + g') := by
  first | exact @GlobalTheory.TopSteps.Repr.smul_add | exact GlobalTheory.TopSteps.Repr.smul_add | (intros; apply GlobalTheory.TopSteps.Repr.smul_add <;> assumption)
