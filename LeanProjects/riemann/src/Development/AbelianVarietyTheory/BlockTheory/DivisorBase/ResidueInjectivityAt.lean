import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def resLow {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) :
    MMap M →ₗ[ℂ] MultilinearMap ℂ (fun ρ : D.what₂.Tau => lowT M ρ) (GA D V → ℂ) :=
  MultilinearMap.compLinearMapₗ fun ρ => (lowT M ρ).subtype

def ResInjAt {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) : Prop :=
  ∀ (i : Fin D.R.m), ∀ U ∈ R.Wall i (sg0 D A),
    (∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, U (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) = 0) → U = 0

def ResInj : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.models_inf → ResInjAt R

theorem ResInj.of_char (h : ResInj) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A) (hR : R.Char F) : ResInjAt R :=
  h D G Pl0 T A Ks R hR.models.inf

end GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt

end
