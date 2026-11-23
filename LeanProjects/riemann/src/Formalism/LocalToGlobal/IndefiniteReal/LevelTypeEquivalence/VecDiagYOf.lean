import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.KerDiag
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.KerDiag

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

open Classical in

structure SideY (t : T) (k : ℕ) : Prop where
  hST : (Yc D k).rank ≤ (Yc D (k + 1)).rank
  step : R.datYt t (k + 1) R.triv = Formalism.IndefR.Fin.stepLev (R.datYt t k R.triv) (R.chi (k + 1)) (Yc D (k + 1)).rank hST
  dat : ∃ (BS : D.what₂.Tau → Matrix (Fin (Yc D k).rank) (Fin (Yc D k).rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin (Yc D (k + 1)).rank) (Fin (Yc D (k + 1)).rank) ℂ) (pS pT : D.what₂.Tau → ℕ),
    IsDatumStep R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) BS BT pS pT (R.ΛY k)
      (R.ΛY (k + 1)) (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) (R.vac k) (R.vY t k)
  sph : Formalism.IndefR.WeilFull.SphInertAtO R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
    (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.ωY t k)
  rS : (Yc D k).rank = (R.datYt t k R.triv).r + (R.datYt t k R.triv).s * (R.datYt t k R.triv).t
  rT : (Yc D (k + 1)).rank = (Yc D k).rank + (R.datYt t k R.triv).t
  odd : Odd (R.datYt t k R.triv).t
  hQ : (R.datYt t k R.triv).Q = R.Q t
  xq : (R.datYt t k R.triv).xq = fun PP => (R.xiR t PP)⁻¹
  hP : (R.datYt t k R.triv).P = Formalism.L2.DIV.LevelP.triv (R.datYt t k R.triv).Pg (R.datYt t k R.triv).r ℂ
  unr : ∀ e, IsIdemSum e ((R.datYt t k R.triv).Pg ∪ R.Q t) →
    Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 ∧
      Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2
  tameG : ∀ PP ∈ (R.datYt t k R.triv).Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
    Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.chi (k + 1) PP) (-1) ∧
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.chi (k + 1) PP) (-1)
  tameQ : ∀ PP ∈ R.Q t, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
    Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.xiR t PP) 1 ∧
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.xiR t PP) 1

open Classical in

structure SideYR (t : T) (k : ℕ) : Prop where
  dat : ∃ (BS : D.what₂.Tau → Matrix (Fin (Yc D k).rank) (Fin (Yc D k).rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin (Yc D (k + 1)).rank) (Fin (Yc D (k + 1)).rank) ℂ) (pS pT : D.what₂.Tau → ℕ),
    IsDatumStep R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) BS BT pS pT (R.ΛY k)
      (R.ΛY (k + 1)) (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) (R.vac k) (R.vY t k)
  sph : Formalism.IndefR.WeilFull.SphInertAtO R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
    (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.ωY t k)
  unr : ∀ e, IsIdemSum e ((R.datYt t k R.triv).Pg ∪ R.Q t) →
    Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 ∧
      Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2
  tameG : ∀ PP ∈ (R.datYt t k R.triv).Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
    Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.chi (k + 1) PP) (-1) ∧
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.chi (k + 1) PP) (-1)
  tameQ : ∀ PP ∈ R.Q t, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
    Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.xiR t PP) 1 ∧
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.xiR t PP) 1

end Formalism.IndefR.Eqv.KerDiag

end
