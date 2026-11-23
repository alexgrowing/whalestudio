import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def kernel (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i))
    (φ : WO (Vc D i) (Wc D i) → ℂ) : ℂ :=
  thetaKO (R.ωP i t) h g φ

def Pinned (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 ∧ R.models_inf ∧ RealDat.models_vpos (D := D) ∧ R.models_cV ∧ R.models_HV ∧ R.models_νV ∧
    R.models_BV ∧ R.models_order ∧ R.thP_ωP ∧ R.thP_vP ∧ R.thP_pt_theta ∧ R.thP_ioP

def FiresAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (x : (R.HV i t).H) : Prop :=
  (∀ (e : LowT (R.MW i (sg0 D A))) (g : GA D (Wc D i)),
    IntegrableOn (fun h => kernel R i t g h (R.ptP i t (R.ioP i e (R.extV i t x h)))) (R.fdV i t) (R.νV i t)) ∧
  ∃ Θ ∈ R.Wall i (sg0 D A), ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
    Θ (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) =
      Lift.thetaPInt (R.νV i t) (R.fdV i t) (kernel R i t) (R.ptP i t) (R.ioP i) (R.extV i t x) (PiTensorProduct.tprod ℂ v)

def Fires (R : RealDat D A Ks) : Prop := ∀ (i : Fin D.R.m) (t : T) (x : (R.HV i t).H), FiresAt R i t x

def ThetaFiresFor (R : RealDat D A Ks) : Prop := Pinned R → Fires R

def ThetaFires : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ThetaFiresFor R

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring

end
