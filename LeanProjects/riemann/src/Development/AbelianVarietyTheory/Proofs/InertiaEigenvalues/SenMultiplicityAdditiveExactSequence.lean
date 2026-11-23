import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GmultTransport

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem sen_eq_sen_pre_add_sen_push : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (N : Lats k n B.m), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, IsLat (N i) → CondC ((F.D B).γ i) (N i) → ∀ x, sen ((F.D B).γ i) (N i) x = sen ((F.D A).γ i) (F.pre A B f N i) x + sen ((F.D C).γ i) (F.push B C p N i) x := by
  intro k G _ _ l n _ _ _ R F A B C f p N hB hf hp hfi hps hex i hN hc x
  have hA : F.Obj A := F.obj_sub A B f hf hfi hB
  have hC : F.Obj C := F.obj_quot B C p hp hps hB
  exact GlobalTheory.PhiGam.SenAdd.main R ((F.D B).γ i) ((F.D A).γ i) ((F.D C).γ i) (F.map A B f i) (F.map B C p i)
    ((F.D B).γ_semi i) (F.map_inj A B f hA hB hf hfi i) (F.map_surj B C p hB hC hp hps i)
    (GlobalTheory.Models.DFun.map_exact_middle F A B C f p hB hf hp hfi hps hex i) (F.map_γ A B f hA hB hf i) (F.map_γ B C p hB hC hp i)
    (N i) hN hc x

end GlobalTheory.Models
