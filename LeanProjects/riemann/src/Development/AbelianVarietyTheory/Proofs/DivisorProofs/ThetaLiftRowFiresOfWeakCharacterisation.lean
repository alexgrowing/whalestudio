import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThetaFireRow
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFiringRowAtConcreteLiftsStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem thetaLiftRow_fires_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → A3.A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R.toRealDat) (hinj : ∀ i t, Function.Injective (R.toRealDat.extV i t)) (IL : RecTie.LiftIds (RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj)), RecTie.ThetaFireRow (RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj) IL := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC e hv tupT hm hTop hinj IL
  exact GlobalTheory.T.thetaFiringRow_at_concreteLifts R.toRealDat F.lv2 tupT hm hTop hinj hC.base e hv IL

end GlobalTheory
