import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigOfSat
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DifferentiableAtChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LevelS
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DirChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm

open NumberField IsDedekindDomain Matrix UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc)
open UpperTheory.V.TR (infGL CuspSub)

namespace GlobalTheory.HenQ

theorem expo_eq_zero_of_pow {K : Type} [Field K] [NumberField K] [IsTotallyReal K] (ξ : Formalism.L2.Host.HChar K) {N : ℕ}
    (hN : 0 < N) (h : ξ ^ N = 1) (v : InfinitePlace K) : TR.expo ξ v = 0 := by
  classical
  have key : ∀ k : ℕ, ∀ z, TR.dchi (ξ ^ k) z = (k : ℂ) * TR.dchi ξ z := by
    intro k
    induction k with
    | zero => intro z; simp [TR.dchi_one]
    | succ k ih => intro z; rw [pow_succ, TR.dchi_mul, ih]; push_cast; ring
  have h1 := key N (Pi.single v 1)
  rw [h, TR.dchi_one] at h1
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  exact (mul_eq_zero.1 h1.symm).resolve_left hN'

end GlobalTheory.HenQ
