import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Premises (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 ∧ R.models_inf ∧ RealDat.models_vpos (D := D) ∧ R.models_cV ∧ R.models_HV ∧ R.models_νV ∧
    R.models_BV ∧ R.models_order ∧ R.thP_ωP ∧ R.thP_vP ∧ R.thP_pt_theta ∧ R.thP_ioP

def kernelP (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i))
    (Φ : WO (Vc D i) (Wc D i) → ℂ) : ℂ :=
  thetaKO (R.ωP i t) h g Φ

def IsThetaMult (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))) : Prop :=
  (∀ x, y x ∈ R.Wall i (sg0 D A)) ∧
    ∃ thP : LinearMap.range (R.extV i t) →ₗ[ℂ] (LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ)),
      Lift.IsThetaP (R.νV i t) (R.fdV i t) (kernelP R i t) (R.ptP i t) (R.ioP i) (LinearMap.range (R.extV i t)) thP ∧
      ∀ (x : (R.HV i t).H) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
        y x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) =
          thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

def ThetaMultExistsFor (R : RealDat D A Ks) : Prop :=
  Premises R → ∀ (i : Fin D.R.m) (t : T), ∃ y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A)), IsThetaMult R i t y

end

def ThetaMultExists (D : D7) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ThetaMultExistsFor R

section Basic₂

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaMultiplicity

end
