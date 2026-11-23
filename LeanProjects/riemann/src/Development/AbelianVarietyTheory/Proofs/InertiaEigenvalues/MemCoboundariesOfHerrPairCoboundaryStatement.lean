import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCoboundariesOfHerrPairCoboundary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (z : G → Fin A.m → k) (b g : ZMod n → Vc k A.m), Repr F A z b g → (b, g) ∈ herrB (F.D A) → z ∈ cob A := by
  first | exact @GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB | exact GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB | (intros; apply GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB <;> assumption)
