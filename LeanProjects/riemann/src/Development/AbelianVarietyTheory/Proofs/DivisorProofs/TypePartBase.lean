import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisedDualSystem

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix

namespace GlobalTheory.LiftLower

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def csumAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) : ℂ :=
  star (fun a => σ (S.basis.repr f a)) ⬝ᵥ (S.H.map σ) *ᵥ fun a => σ (S.basis.repr g a)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levSW (i : Fin D.R.m) : Set (GA D (Wc D i)) := levS _ (R.βW i) (R.datWp i R.triv)

abbrev chiW (i : Fin D.R.m) : GA D (Wc D i) → ℂ := Lev.levChi _ (R.βW i) (R.datWp i R.triv)

def partH (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) : Submodule ℂ (R.HW i σ).H :=
  (partFull R.θ (R.MW i σ) (levSW R i) (chiW R i) (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) c).comap (R.HW i σ).e

def IsNormSys (i : Fin D.R.m) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) : Prop :=
  ∀ P d, (¬ ∃ Rp, Hecke₂ (Wc D i) (levSW R i) (chiW R i) (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P d Rp) → c P d = 0

def projH (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : (R.HW i σ).H →ₗ[ℂ] (R.HW i σ).H :=
  ∑ g, RealDat.eC (A := A) σ g • R.gW i σ g

variable (D) in

def hookPlus (i : Fin D.R.m) : ℝ :=
  ∑ ρ : D.what₂.Tau, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D i ρ) (aPl D i (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D i ρ) ρ) : ℝ)

structure NumTie (F : Face D A) (b : ℝ) : Prop where
  sizes : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes D i b
  main : ∀ i, (F.Zsc (R.toCx F).zs).l6m i = hookPlus D i
  unit : (F.Zsc (R.toCx F).zs).l6u = (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D b

variable {R}

theorem Q_base (h : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro PP hPP
  refine (h.Q_ram A.μ0 PP).2 (Or.inl hPP) ?_
  rw [h.xi_base]
  intro x _
  rfl

theorem typePart_base (h : R.toLevCh.Is A.μ0) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart R i σ A.μ0 R.triv c = partH R i σ c := by
  classical
  have e : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS R A.μ0 = GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF
    rw [Q_base h]
    congr 1
    ext; simp
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart partH
  rw [e]

theorem e_projH (h : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    (R.HW i σ).e (projH R i σ x) = postOn _ (R.eWf i σ) ((R.HW i σ).e x) := by
  unfold projH RealDat.eWf gaL
  rw [LinearMap.sum_apply, map_sum]
  ext v g
  simp only [LinearMap.smul_apply, map_smul, h i σ, postOn_apply, LinearMap.sum_apply, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply]
  rfl

end GlobalTheory.LiftLower

end
