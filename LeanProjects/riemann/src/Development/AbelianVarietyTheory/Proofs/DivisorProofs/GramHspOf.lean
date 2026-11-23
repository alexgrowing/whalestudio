import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField

namespace GlobalTheory.WeilSchrodinger

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def sesq {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) :
    (Fin k → D.host.E) →ₗ⋆[D.host.E] (Fin k → D.host.E) →ₗ[D.host.E] D.host.E :=
  Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) G

def hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm) (nd : (sesq D G).Nondegenerate)
    (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D where
  V := Fin k → D.host.E
  hT := sesq D G
  herm := herm
  nondeg := nd
  rank := k
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := sg
  L0 := L
  standardTuple_isLattice := hL
  baseLattice_isUnimodular := hU

variable {D}

theorem gram_hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm)
    (nd : (sesq D G).Nondegenerate) (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) :
    (hspOf D G herm nd L hL hU sg).gram = G := by
  funext i j
  have e : ∀ m : Fin k, Pi.basisFun D.host.E (Fin k) m = Pi.single m 1 := fun m => Pi.basisFun_apply _ _ m
  simp only [HSpace.gram, hspOf, sesq]
  erw [e i, e j]
  exact Matrix.toLinearMapₛₗ₂'_single (R := D.host.E) (starRingEnd D.host.E) (RingHom.id D.host.E) G i j

end GlobalTheory.WeilSchrodinger

end
