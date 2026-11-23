import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfQdetMem
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CuspRep.SplitDeriv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem hasDerivAt_scalar_exp :
    HasDerivAt (fun t : ℝ =>
      toL (Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))).val)
      (fun i j => if i = j then (1 : Cinf E) else 0) 0 := by
  rw [hasDerivAt_pi]; intro i
  rw [hasDerivAt_pi]; intro j
  rw [hasDerivAt_pi]; intro w
  by_cases h : i = j
  · subst h
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have h2 := h1.cexp
    simpa [toL, Matrix.scalar_apply, Matrix.diagonal_apply, expU] using h2
  · simpa [toL, Matrix.scalar_apply, Matrix.diagonal_apply, h] using hasDerivAt_const (0 : ℝ) (0 : ℂ)

open GlobalTheory.UnitaryBC in

theorem hasDerivAt_splitCentre (ψ : Sm E a) (g : GA E a) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ψ.1 (g * splitCentre E a t))
      ((lie E a (fun i j => if i = j then (1 : Cinf E) else 0) ψ).1 (g * splitCentre E a s)) s := by
  have h0 : Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext i j w
    by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, expU, Matrix.one_apply, h]
  have h := hasDerivAt_curve ψ (g * splitCentre E a s)
    (fun t => Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ)))
    _ h0 hasDerivAt_scalar_exp
  have h' := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h)
  rw [lie_apply]
  refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  change ψ.1 (g * splitCentre E a t) = ψ.1 (g * splitCentre E a s * splitCentre E a (t - s))
  rw [mul_assoc, ← splitCentre_add, add_sub_cancel]

end GlobalTheory.CuspRep.SplitDeriv
