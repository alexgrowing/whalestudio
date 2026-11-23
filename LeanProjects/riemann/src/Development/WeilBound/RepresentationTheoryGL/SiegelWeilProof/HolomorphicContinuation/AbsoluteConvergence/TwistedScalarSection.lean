import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjOp

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def aZ {n : ℕ} (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  fromBlocks (diagonal fun j => Complex.exp (z * X j)) 0 0 (diagonal fun j => Complex.exp (-(z * X j)))

def twistedScalarSection {n : ℕ} (p q : ℕ) (e : ℤ) (M : M2 n) : ℂ := M.det ^ e * f0 p q M

def TSBFacts : Prop :=
  CayleyBlocksInvertible → ∀ (n p q : ℕ) (e : ℤ),
    CompactSpace (KR n) ∧ Continuous (mR : GR n → M2 n) ∧ Continuous (F0 p q e : GR n → ℂ) ∧
    (∀ (X : Fin n → ℝ) (t : ℝ), ∃ a : GR n, IsDil X t a) ∧
    (∀ (X : Fin n → ℝ) (t : ℝ) (a : GR n), IsDil X t a → mR a = aZ X t) ∧
    ∀ (X : Fin n → ℝ) (C : Set (GR n)), IsCompact C → ∃ U : Set ℂ, IsOpen U ∧ (∀ t : ℝ, (t : ℂ) ∈ U) ∧
      ContinuousOn (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) (C ×ˢ U) ∧
      ∀ y ∈ C, DifferentiableOn ℂ (fun z => twistedScalarSection p q e (mR y * aZ X z)) U

end PositivityTheory.Rg.Sw.AbsSt
