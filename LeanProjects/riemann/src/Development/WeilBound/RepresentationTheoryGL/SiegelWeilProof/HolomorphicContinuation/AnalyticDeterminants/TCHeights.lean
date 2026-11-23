import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCBlockA

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem iter_cast {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : V → ℂ) (x : V) {m m' : ℕ} (h : m = m')
    (v : Fin m → V) : iteratedFDeriv ℂ m f x v = iteratedFDeriv ℂ m' f x (v ∘ Fin.cast h.symm) := by
  subst h
  rfl

end PositivityTheory.Rg.Sw.LVs.TC
