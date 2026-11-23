import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DefiniteIndexDimensionCounts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)

namespace GlobalTheory.DefFree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

instance factTypePrime (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

theorem finE_mem (V : HSp D) (h : GA D V) : finE V h ∈ UA D.sp.cm V.gram := by
  have h0 : matHom V h ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    let h' : HR (AF D.host.F) D.sp.cm.sig V.gram := h
    exact h'.2
  have h1 := Formalism.UG.P.bc_mem _ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig)
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom ?c1 _ _ h0
  have h2 := Formalism.UG.P.bc_mem _ (Formalism.UG.sigR D.sp.cm.sig (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) (swapAE D) ?c2 _ _ h1
  convert h2 using 1
  case e'_5 => rfl
  case e'_4 =>
    unfold UA Formalism.UG.UPts
    congr 1
  case c2 =>
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [swapAE, sigR, Formalism.UG.sigR]
    | add x y hx hy => simp only [RingHom.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
  case c1 =>
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add x y hx hy => simp only [RingHom.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]

def finU (V : HSp D) : GA D V →* UA D.sp.cm V.gram := (finE V).codRestrict _ (finE_mem V)

theorem coe_finU (V : HSp D) (h : GA D V) : (finU V h : GL (Fin V.rank) (EAf D)) = finE V h := rfl

def clsA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (h : GA D V) : Cl D.sp.cm V.gram K :=
  Quotient.mk'' (finU V h)

def evAt {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : GA D V) :
    MMap M →ₗ[ℂ] MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ where
  toFun T := (LinearMap.proj h : (GA D V → ℂ) →ₗ[ℂ] ℂ).compMultilinearMap T
  map_add' T T' := by ext v; simp
  map_smul' c T := by ext v; simp

theorem evAt_apply {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : GA D V) (T : MMap M) (v : M.Vec) :
    evAt M h T v = T v h := rfl

def eig {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (P : Subgroup G) (χ : P → ℂ) :
    Submodule ℂ M :=
  ⨅ g : P, LinearMap.ker (ρ g - χ g • LinearMap.id)

theorem mem_eig {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] {ρ : Representation ℂ G M} {P : Subgroup G}
    {χ : P → ℂ} {x : M} : x ∈ eig ρ P χ ↔ ∀ g : P, ρ g x = χ g • x := by
  simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

abbrev GProd (D : D7) : Type :=
  (D.nd.PlG 0 → GlobalTheory.BadShare.GG (D.host.g 0) D.R.r) × (D.nd.PlG 1 → GlobalTheory.BadShare.GG (D.host.g 1) D.R.r)

end GlobalTheory.DefFree

end
