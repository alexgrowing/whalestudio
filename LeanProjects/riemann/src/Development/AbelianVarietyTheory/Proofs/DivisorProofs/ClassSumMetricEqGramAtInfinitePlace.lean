import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFormsOfToH
import Formalism.LocalToGlobal.Columns.RowFormsRat
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder
open Formalism.DivisionValues GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ClassSumCoord

theorem ipAt_eq_gram : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (T : Formalism.L2.Col.GSD K) (h : T.Ok), T.Rat → ∀ (v : InfinitePlace K) (φ : T.EqFun), T.ipAt h v φ.1 φ.1 = star (fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) ⬝ᵥ ((T.toCSD h).H.map v.embedding *ᵥ fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) := by
  intro K _ _ _ T h R v φ
  letI := h.fintypeCl
  have hRc : (T.toCSD h).Rat := T.toCSDOf_rat h R T.outSec
  have hb := csd_hasRatBasis _ hRc
  have e : GlobalTheory.PeriodClassSum.coordAt T v φ.1 = GlobalTheory.PeriodOnStep.coAt (T.toCSD h) v (T.res h φ).1 := rfl
  rw [GlobalTheory.PeriodClassSum.ipAt_eq, e, GlobalTheory.PeriodOnStep.H_map _ v hb, GlobalTheory.PeriodOnStep.wForm_sum,
    GlobalTheory.PeriodOnStep.coAt_sum (T.toCSD h) v (T.res h φ)]
  simp only [Basis.equivFun_apply]
  rfl

end GlobalTheory.ClassSumCoord
