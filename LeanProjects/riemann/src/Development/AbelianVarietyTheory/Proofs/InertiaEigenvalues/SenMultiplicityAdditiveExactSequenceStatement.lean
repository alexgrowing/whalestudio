import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequence
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senMultiplicity_additive_exact_sequence : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (N : Lats k n B.m), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, IsLat (N i) → CondC ((F.D B).γ i) (N i) → ∀ x, sen ((F.D B).γ i) (N i) x = sen ((F.D A).γ i) (F.pre A B f N i) x + sen ((F.D C).γ i) (F.push B C p N i) x := by
  first | exact @GlobalTheory.Models.sen_eq_sen_pre_add_sen_push | exact GlobalTheory.Models.sen_eq_sen_pre_add_sen_push | (intros; apply GlobalTheory.Models.sen_eq_sen_pre_add_sen_push <;> assumption)
