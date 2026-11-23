import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SepCountNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.DegreeFormula.PointDegree.FlagDeg
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst
open Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst.Polar

open MvPolynomial

def lamS {Ψ : Type} {N e : ℕ} (w : Fin e → Ψ × Fin N) (S : Finset (Fin e)) : Ψ → Fin N → ℝ :=
  fun τ k => ∑ r ∈ S, if (w r).1 = τ ∧ k ≤ (w r).2 then (1 : ℝ) else 0

end GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst.Polar
