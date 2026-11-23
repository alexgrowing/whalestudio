import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.NFLeTwoMulTSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SizeOK (D : D7) : Prop := 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def transl (R : RealDat D A Ks) (i : Fin D.R.m) (g : G) :
    MMap (R.MW i (sg0 D A)) →ₗ[ℂ] MMap (R.MW i (sg0 D A)) :=
  postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g))

def thetaTranslates (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (MMap (R.MW i (sg0 D A))) :=
  {y | ∃ (g : G) (x : (R.HV i t).H), y = transl R i g (R.thF i t x)}

def SpanAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  Submodule.span ℂ (thetaTranslates R i t) = R.Wall i (sg0 D A)

def goodModel (R : RealDat D A Ks) (i : Fin D.R.m) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (R.Wat i (sg0 D A) R.triv).comap (R.HW i (sg0 D A)).e

def GoodRangeAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  LinearMap.range (R.thG i t) = goodModel R i

def ThetaSpan (R : RealDat D A Ks) (F : Face D A) : Prop :=
  SizeOK D → R.Char F → ∀ i : Fin D.R.m, SpanAt R i A.μ0

def ThetaGoodRange (R : RealDat D A Ks) (F : Face D A) : Prop :=
  SizeOK D → R.Char F → ∀ (i : Fin D.R.m) (t : T), GoodRangeAt R i t

def ThetaGoodRangeGap (R : RealDat D A Ks) (F : Face D A) : Prop :=
  R.Char F → ∀ (i : Fin D.R.m) (t : T), GoodRangeAt R i t

theorem range_eq_comap_iff {X H M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup H] [Module ℂ H] [AddCommGroup M]
    [Module ℂ M] (e : H →ₗ[ℂ] M) (f : X →ₗ[ℂ] H) (p : X →ₗ[ℂ] M) (U : Submodule ℂ M) (hinj : Function.Injective e)
    (hle : U ≤ LinearMap.range e) (hc : ∀ x, e (f x) = p x) :
    LinearMap.range f = U.comap e ↔ LinearMap.range p = U := by
  have hcomp : e ∘ₗ f = p := LinearMap.ext hc
  rw [← hcomp, LinearMap.range_comp]
  constructor
  · intro h
    rw [h, Submodule.map_comap_eq_self hle]
  · intro h
    rw [← h, Submodule.comap_map_eq_of_injective hinj]

set_option maxHeartbeats 1000000 in

theorem goodRangeAt_iff {R : RealDat D A Ks} (hW : R.models_HW) (hG : R.thP_thG) (i : Fin D.R.m) (t : T) :
    GoodRangeAt R i t ↔
      LinearMap.range (postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) ∘ₗ R.thF i t) = R.Wat i (sg0 D A) R.triv :=
  range_eq_comap_iff (R.HW i (sg0 D A)).e (R.thG i t) _ (R.Wat i (sg0 D A) R.triv) (hW i (sg0 D A)).1
    (le_of_le_of_eq inf_le_left (hW i (sg0 D A)).2.1.symm) (fun x => hG i t x)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize

end
