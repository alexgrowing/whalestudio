import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe.KeepD

variable {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X)

set_option maxHeartbeats 4000000 in

theorem toTerm_eTT (u u' : D.what₂.Word) (s : TT Y u u') : (eTT Z Y u u' s).toTerm = eRT Z Y u u' s.toTerm := (by with_unfolding_all exact (Eq.refl (eRT Z Y u u' s.toTerm) :))

set_option maxHeartbeats 4000000 in

def eFib (u u' : D.what₂.Word) (t : RT Y u u') : fib Y t ≃ fib (reY Z Y) (eRT Z Y u u' t) :=
  Equiv.subtypeEquiv (eTT Z Y u u') fun s => by
    rw [toTerm_eTT]
    exact (eRT Z Y u u').injective.eq_iff.symm

set_option maxHeartbeats 4000000 in

theorem aT_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u u' : D.what₂.Word) (s : TT Y u u') (x : ColT (h.shInj u')) :
    eCure Z h h' u (aT h u u' s x) = aT h' (wd Z u) (wd Z u') (eTT Z Y u u' s) (eCure Z h h' u' x) := (by with_unfolding_all exact (
  Eq.refl (aT h u u' s x) :))

set_option maxHeartbeats 4000000 in

theorem aR_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u u' : D.what₂.Word) (t : RT Y u u') (x : ColT (h.shInj u')) :
    eCure Z h h' u (aR h u u' t x) = aR h' (wd Z u) (wd Z u') (eRT Z Y u u' t) (eCure Z h h' u' x) := by
  letI := h.fibFT t
  letI := h'.fibFT (eRT Z Y u u' t)
  unfold aR
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, map_sum]
  exact Fintype.sum_equiv (eFib Z Y u u' t) _ _ fun s => aT_keep Z Y u u' s.1 x

set_option maxHeartbeats 4000000 in

theorem pu_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u : D.what₂.Word) (x : ColT (h.shInj u)) :
    eHHre Z X (puC h u x) = puC h' (wd Z u) (eCure Z h h' u x) := (by with_unfolding_all exact (Eq.refl (puC h u x) :))

set_option maxHeartbeats 4000000 in

theorem vol_keep (u : D.what₂.Word) : Y.volN u = (reY Z Y).volN u ∧ Y.volH u = (reY Z Y).volH u := by
  constructor
  · exact (by with_unfolding_all exact (Eq.refl (Y.volN u) :))
  · exact (by with_unfolding_all exact (Eq.refl (Y.volH u) :))

end GlobalTheory.Mem.SRe.KeepD

namespace GlobalTheory.Mem.SRe

set_option maxHeartbeats 4000000 in

theorem keep_pu_vol_aR : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y)), (∀ u x, eHHre Z X (puC h u x) = puC h' (wd Z u) (eCure Z h h' u x)) ∧ (∀ u, Y.volN u = (reY Z Y).volN u ∧ Y.volH u = (reY Z Y).volH u) ∧ ∀ u u' (t : RT Y u u') x, eCure Z h h' u (aR h u u' t x) = aR h' (wd Z u) (wd Z u') (eRT Z Y u u' t) (eCure Z h h' u' x) :=
  fun _ Z _ Y _ _ => ⟨fun u x => KeepD.pu_keep Z Y u x, fun u => KeepD.vol_keep Z Y u,
    fun u u' t x => KeepD.aR_keep Z Y u u' t x⟩

end GlobalTheory.Mem.SRe
