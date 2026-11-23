import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointTwistedHermUnimodularEqSelfDual
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basePoint_twistedHerm_unimodular_eq_selfDual : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → ∀ ε : B.A, (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧ ∀ x : B.Aˣ, B.σ (x : B.A) = x → {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  first | exact @GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any | exact GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any | (intros; apply GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any <;> assumption)
