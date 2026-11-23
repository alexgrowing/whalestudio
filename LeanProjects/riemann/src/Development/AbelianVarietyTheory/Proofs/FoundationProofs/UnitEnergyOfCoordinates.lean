import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCoord

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Cx
open GlobalTheory.FormTies GlobalTheory.OnTies
open GlobalTheory.OntoChain (coordMap thetaMat thetaOp liftLvl liftSub supLat Mir mirIncl uni mirToGL)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Build

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df}
  {P : Type} [Group P] [Finite P] {c : OnConst}

def withCoord (O : OnObj S P c) (φ : ∀ j, (Fin (S.dW j) → K) →ₗ[K] (Fin (O.nZ j) → K)) : OnObj S P c := { O with φ := φ }

def builtData (O : OnObj S P c) : IndefData Df := { S with err0 := O.errOn }

def overBuilt (O : OnObj S P c) : OnObj (builtData O) P c := { O with }

def budgetNc (Rk : Ranks) (sc : Scale) (T2 : ℕ) : ℝ :=
  (T2 : ℝ) * Rk.k * sc.b * sc.x ^ sc.eps / (Rk.n * (Rk.n * sc.x ^ (-sc.eps)))

def boundUnit (Rk : Ranks) (sc : Scale) (T2 : ℕ) : ℝ :=
  sc.x ^ sc.eps * ((Rk.f : ℝ) * Rk.m * sc.b * sc.x ^ sc.eps + budgetNc Rk sc T2)

def TieSizes (O : OnObj S P c) (Rk : Ranks) (sc : Scale) (T2 : ℕ) : Prop :=
  O.x = sc.x ∧ O.eps = sc.eps ∧ O.f = Rk.f ∧ O.m = Rk.m ∧ O.Nc = budgetNc Rk sc T2

def TieUnit (Z : IndefScale Bs) (Rk : Ranks) (sc : Scale) (T2 : ℕ) : Prop := Z.E1u = boundUnit Rk sc T2

example (O : OnObj S P c) (Z : IndefScale Bs) (Rk : Ranks) (sc : Scale) (T2 : ℕ) :
    TieSizes ({ O with x := sc.x, eps := sc.eps, f := Rk.f, m := Rk.m, Nc := budgetNc Rk sc T2 } : OnObj S P c) Rk sc T2 ∧
      TieUnit { Z with E1u := boundUnit Rk sc T2 } Rk sc T2 := ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

end Build

end GlobalTheory.OnCoord
