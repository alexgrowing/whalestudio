import Formalism.PeriodIntegrals.LatCountG
import Formalism.HarderNarasimhan.StatementPl
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.TheoremCountStatementOfGeometry

noncomputable section

namespace Formalism.L2.S.S7.GeoObj

open NumberField Module
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates

variable (I : AutInst)

def basisE : Basis (Fin I.n) I.E (Fin I.n → I.E) := Pi.basisFun I.E (Fin I.n)

def cmat (x : I.GA) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ := uMat (x.1 v)⁻¹ * (I.P v)⁻¹

open Classical in

def frame (x : I.GA) (w : InfinitePlace I.E) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  if w.embedding = I.φ (w.comap (algebraMap I.F I.E)) then (cmat I x (w.comap (algebraMap I.F I.E)))⁻¹
  else ((cmat I x (w.comap (algebraMap I.F I.E))).map (starRingEnd ℂ))⁻¹

def lat (x : I.GA) : Submodule (𝓞 I.E) (Fin I.n → I.E) := Submodule.span (𝓞 I.E) (PI.LatCountG.latSet I x)

def rho (x : I.GA) := Formalism.HermitianLatticesTheory.realize (basisE I) (frame I x)

def cE : ℝ := Real.log 2 / 2 - Formalism.HN.logDisc I.E / (2 * (Module.finrank ℚ I.E : ℝ))

def stepLe (x : I.GA) (s : ℝ) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Formalism.HN.hnStep (rho I x) (lat I x) (cE I - Real.log s)

def rkLe (x : I.GA) (s : ℝ) : ℕ := Formalism.HN.rkK (stepLe I x s)

def IsLowType (x : I.GA) (J : ℕ) (c : Composition J) (t : Fin c.length → ℝ) : Prop :=
  t ∈ cn_Reg c.length ∧
    ∀ s : ℝ, 0 < s → s < 1 / 2 → rkLe I x s = ∑ i, if t i ≤ s then c.blocksFun i else 0

def BaseVolumeRepresentatives : Set I.GA := {x | ∀ s : ℝ, 0 < s → s < 1 / 2 → rkLe I x s = 0}

def strSet (J : ℕ) (c : Composition J) : Set I.GA := {x | 1 ≤ J ∧ ∃ t, IsLowType I x J c t}

open Classical in

def tauT (J : ℕ) (c : Composition J) (x : I.GA) : Fin c.length → ℝ :=
  if h : ∃ t, IsLowType I x J c t then h.choose else fun _ => 1 / 4

def flagT (J : ℕ) (c : Composition J) (x : I.GA) (i : Fin c.length) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  stepLe I x (tauT I J c x i)

def tau1 (x : I.GA) : ℝ := if I.n = 0 then 1 / 2 else PI.LatCountG.tau1 I x

end Formalism.L2.S.S7.GeoObj

namespace Formalism.L2.S.S7.GeoObj

open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates

def obj (X : CData) (kp : ∀ J : ℕ, Composition J → ℝ) : CSize X where
  tau1 := tau1 X.I
  I0 := BaseVolumeRepresentatives X.I
  str := strSet X.I
  tau := tauT X.I
  kap := kp

end Formalism.L2.S.S7.GeoObj

end
