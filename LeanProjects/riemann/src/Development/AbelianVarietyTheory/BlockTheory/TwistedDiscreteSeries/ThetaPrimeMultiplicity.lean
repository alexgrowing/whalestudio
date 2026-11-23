import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaPrimeMultiplicity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section At

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def IsThetaPrimeMult (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))) : Prop :=
  (∀ x, y x ∈ R.Wall i (sg0 D A)) ∧
    ∃ thP : LinearMap.range (R.extV i t) →ₗ[ℂ] (LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ)),
      Lift.IsThetaP (R.νV i t) (R.fdV i t)
          (fun (g : GA D (Wc D i)) (h : GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) => thetaKO (R.ωP i t) h g f)
          (R.ptP i t) (R.ioP i) (LinearMap.range (R.extV i t)) thP ∧
        ∀ (x : (R.HV i t).H) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
          y x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) =
            thP ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v)

def ThetaPrimeExistsFor (R : RealDat D A Ks) : Prop :=
  R.toLevCh.Is A.μ0 → R.fam_tie → R.IsModels → R.thP_ωP → R.thP_vP → R.thP_pt_theta → R.thP_ioP →
    ∀ (i : Fin D.R.m) (t : T), ∃ y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A)), IsThetaPrimeMult R i t y

set_option maxHeartbeats 1000000 in

theorem IsThetaPrimeMult.integral {R : RealDat D A Ks} {i : Fin D.R.m} {t : T}
    {y : (R.HV i t).H →ₗ[ℂ] MMap (R.MW i (sg0 D A))} (h : IsThetaPrimeMult R i t y)
    (x : (R.HV i t).H) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    IntegrableOn (fun u : GA D (Vc D i) =>
        R.ωP i t (u, g) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) (R.extV i t x u))) 0) (R.fdV i t) (R.νV i t) ∧
      y x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) g =
        ∫ u in R.fdV i t, R.ωP i t (u, g) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) (R.extV i t x u))) 0 ∂(R.νV i t) := by
  obtain ⟨-, thP, h1, h2⟩ := h
  have e1 := h1.integ ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v) g
  have e2 := h1.eq ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ v) g
  have e3 : (((R.extV i t).rangeRestrict x : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) = R.extV i t x := rfl
  simp only [Lift.thetaPInt, thetaKO, e3] at e1 e2
  exact ⟨e1, (congrFun (h2 x v) g).trans e2⟩

theorem isThetaPrimeMult_thF_iff (R : RealDat D A Ks) :
    (∀ i t, IsThetaPrimeMult R i t (R.thF i t)) ↔ R.thP_thF_mem ∧ R.thP_thF :=
  ⟨fun h => ⟨fun i t => (h i t).1, fun i t => (h i t).2⟩, fun h i t => ⟨h.1 i t, h.2 i t⟩⟩

end At

def ThetaPrimeExists (D : D7) : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ThetaPrimeExistsFor R

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaPrimeMultiplicity

end
