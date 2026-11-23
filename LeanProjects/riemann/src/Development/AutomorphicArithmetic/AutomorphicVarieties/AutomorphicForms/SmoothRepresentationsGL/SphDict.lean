import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.SphDefs
import GroundTheory.GlobalFields.CompletionAtPlace.Inertia

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem sqrt_pow (q r n : ℕ) (hq : q ≠ 0) (h : r ≤ n) :
    (((NNReal.sqrt (q : NNReal) : NNReal) : ℝ) : ℂ) ^ (r * (n - r)) =
      (q : ℂ) ^ (((r : ℂ) * ((n : ℂ) - r)) / 2) := by
  have e : ((r : ℂ) * ((n : ℂ) - r)) / 2 = (1 / 2 : ℂ) * ((r * (n - r) : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub h]; ring
  rw [e, Complex.cpow_mul_nat]
  congr 1
  rw [Real.coe_sqrt, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  simp

theorem UpperTheory.V.Af.Smo.sphDict :
    UpperTheory.V.Af.Smo.SphDict := by
  intro E _ _ n w
  refine ⟨?_, ?_, fun r hr => ?_, fun u hu => ⟨fun i _ => ⟨hu.2 i, fun j hj => hu.1 hj⟩, fun ψ => ?_⟩⟩
  · have hO : Formalism.UG.Ov E w = (ValuativeRel.valuation (w.adicCompletion E)).integer :=
      Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm
    change _ = Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w)
    rw [hO]
    rfl
  · exact GroundTheory.Global.valued_of_irreducible_integer w (GLnLocal.irreducible_uniformizer _)
  · have hq : Spherical.qF (w.adicCompletion E) = Formalism.UG.qV E w := by
      unfold Spherical.qF Formalism.UG.qV
      rw [GroundTheory.Global.natCard_residueField_integer, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    unfold Spherical.sqrtQ
    rw [hq]
    exact sqrt_pow _ r n (by
      unfold Formalism.UG.qV
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot) hr
  · simp only [Whittaker.psiN, Whittaker.superdiagSum, supN, eq_comm]
