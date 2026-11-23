import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exact_map_of_exact : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, Function.Exact (F.map A B f i) (F.map B C p i) := by
  first | exact @GlobalTheory.Models.DFun.map_exact_middle | exact GlobalTheory.Models.DFun.map_exact_middle | (intros; apply GlobalTheory.Models.DFun.map_exact_middle <;> assumption)
