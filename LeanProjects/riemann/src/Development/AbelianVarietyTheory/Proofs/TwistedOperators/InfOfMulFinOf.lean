import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DefStep

variable {D : D7}

def finOf (V : HSp D) (g : GA D V) : GfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2

def infOf (V : HSp D) (g : GA D V) : GinfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).1

theorem infOf_mul_finOf (V : HSp D) (g : GA D V) : ((infOf V g : GinfC V) : GA D V) * (finOf V g : GA D V) = g :=
  (GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g

def IsFinReal {V : HSp D} {Wsp : Type} [AddCommGroup Wsp] [Module ℂ Wsp] (ρ : GA D V →* Module.End ℂ Wsp)
    (F : GA D V → ℂ) (Λ : Module.Dual ℂ Wsp) (v : GfC V → Wsp) : Prop :=
  ∀ g, F g = Λ (ρ g⁻¹ (v (finOf V g)))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def frGL (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (τ : D.what₂.Tau) : GL (Fin (G.V X).rank) ℂ :=
  Formalism.UG.bc (tauE D τ) (fr X)

def realIn (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) :
    GA D (G.V X) →* (D.what₂.Tau → GL (Fin (G.V X).rank) ℂ) :=
  MonoidHom.pi fun τ ↦ (MulAut.conj (frGL fr X τ)⁻¹).toMonoidHom.comp
    ((Pi.evalMonoidHom (fun _ : D.what₂.Tau ↦ GL (Fin (G.V X).rank) ℂ) τ).comp (GlobalTheory.CoefModel.realGL θ (G.V X)))

def realAct (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) :
    GA D (G.V X) →* Module.End ℂ (VV ℂ (wt G X)) :=
  (rhoK (wt G X)).comp (invTrK.comp (realIn θ fr X))

theorem realAct_fin (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) {g : GA D (G.V X)}
    (hg : g ∈ GfC (G.V X)) : realAct θ fr X g = 1 := by
  have h : GlobalTheory.CoefModel.realGL θ (G.V X) g = 1 := by
    funext τ
    show Formalism.UG.bc (θ τ) (infHom (G.V X) g) = 1
    rw [show infHom (G.V X) g = 1 from hg, map_one]
  have h2 : realIn θ fr X g = 1 := by
    funext τ
    simp [realIn, h]
  rw [realAct, MonoidHom.comp_apply, MonoidHom.comp_apply, h2, map_one, map_one]

end GlobalTheory.DefStep

namespace GlobalTheory.DefStep
variable {D : D7}

theorem split_symm_eq (V : HSp D) {g : GA D V} (a : GinfC V) (b : GfC V) (h : (a : GA D V) * b = g) :
    (GlobalTheory.AdelicSplit.splitEquiv V).symm g = (a, b) :=
  (GlobalTheory.AdelicSplit.splitEquiv V).symm_apply_eq.2 h.symm

theorem finOf_fin (V : HSp D) (b : GfC V) : finOf V b = b := by
  rw [finOf, split_symm_eq V 1 b (one_mul _)]

theorem finOf_mul_inf (V : HSp D) (g : GA D V) (k : GinfC V) : finOf V (g * k) = finOf V g := by
  have h : ((infOf V g * k : GinfC V) : GA D V) * (finOf V g : GA D V) = g * k := by
    have hc := GlobalTheory.AdelicSplit.commute_GinfC_GfC V k.2 (finOf V g).2
    conv_rhs => rw [← infOf_mul_finOf V g]
    rw [Subgroup.coe_mul, mul_assoc, hc, ← mul_assoc]
  rw [finOf, split_symm_eq V _ _ h]

theorem finOf_mul_fin (V : HSp D) (g : GA D V) (k : GfC V) : finOf V (g * k) = finOf V g * k := by
  have h : ((infOf V g : GinfC V) : GA D V) * ((finOf V g * k : GfC V) : GA D V) = g * k := by
    rw [Subgroup.coe_mul, ← mul_assoc, infOf_mul_finOf]
  rw [finOf, split_symm_eq V _ _ h]

end GlobalTheory.DefStep

end
