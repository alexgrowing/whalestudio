import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ThetaKernelFiring
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaPrimeMultOfFiresAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.ThetaFiresOfMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1000000 in

theorem exists_isThetaMult_of_firesAt {R : RealDat D A Ks} {i : Fin D.R.m} {t : T}
    (h : ∀ x, FiresAt R i t x) : ∃ y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A)), IsThetaMult R i t y :=
  GlobalTheory.ThetaFiresLinear.exists_linear_lift (lowT (R.MW i (sg0 D A))) (R.Wall i (sg0 D A)) (R.νV i t) (R.fdV i t)
    (kernel R i t) (R.ptP i t) (GlobalTheory.ThetaFiresLinear.kernelL R i t)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t))
    (fun _ _ _ => rfl) (fun _ => rfl) (R.ioP i) (R.extV i t) h

end GlobalTheory.ThetaFiresOfMult

end
