import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeTransferRankOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LocalDataValues
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VectorLevelCharacters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsDCOfMemDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeClassSums

section Linear

variable {L : Type} [Field L] {σ : L →+* ℂ} {H : Type} [AddCommGroup H] [Module ℂ H]

def carried {X : Type} [AddCommGroup X] [Module ℂ X] {n : ℕ} (j : (Fin n → L) →ₛₗ[σ] H) (e : H →ₗ[ℂ] X) {I : Type}
    (p : I → Prop) (T : I → X →ₗ[ℂ] X) (c : ℂ) : Submodule L (Fin n → L) where
  carrier := {y | ∃ y', ∀ a, p a → e (j y') = c • T a (e (j y))}
  add_mem' := by
    rintro x y ⟨x', hx⟩ ⟨y', hy⟩
    exact ⟨x' + y', fun a ha => by simp only [map_add, hx a ha, hy a ha, smul_add]⟩
  zero_mem' := ⟨0, fun a _ => by simp⟩
  smul_mem' := by
    rintro s x ⟨x', hx⟩
    exact ⟨s • x', fun a ha => by rw [map_smulₛₗ, map_smul, hx a ha, map_smulₛₗ, map_smul, map_smul, smul_comm]⟩

open Formalism.L2.Pj.KsHecke

end Linear

section Group

open Formalism.IndefR.Bridge

variable {G : Type} [Group G]

end Group

section Row

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
  Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def ReadOverLLAt (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : Prop :=
  ∃ hL : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL),
    ∀ Rc, IsCosetSys R i P k Rc → ReadAs R i P k Rc hL

def ReadOverLL (i : Fin D.R.m) : Prop :=
  ∀ P : Pl D.host.E, GoodPlace R P → ∀ k : ℕ, k ≤ D.R.r → ReadOverLLAt R i P k

variable {R}

set_option maxHeartbeats 1000000 in

theorem span_jV (hV : R.models_HV) (hj : R.models_jV) (i : Fin D.R.m) (t : T0) : Submodule.span ℂ (Set.range (R.jV i t)) = ⊤ := by
  apply Submodule.map_injective_of_injective (hV i t).1
  rw [Submodule.map_span, Submodule.map_top, (hV i t).2.1, ← Set.range_comp]
  have h1 : (⇑(R.HV i t).e ∘ ⇑(R.jV i t)) = ⇑((R.B.L i t).pres.extL) := funext fun x => hj i t x
  rw [h1]
  exact GlobalTheory.PresBasic.ext_span (R.B.L i t).pres

end Local

section Comparison₂

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

end Comparison₂

end Row

end GlobalTheory.HeckeClassSums
