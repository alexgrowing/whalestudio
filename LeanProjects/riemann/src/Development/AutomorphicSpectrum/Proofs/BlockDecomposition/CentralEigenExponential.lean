import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.Clozel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

def scalarCurve (s : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (s : ℂ))

theorem scalarCurve_zero : scalarCurve E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 :=
    Units.ext (funext fun _ => by simp [expU])
  rw [scalarCurve, h, map_one]

theorem hasDerivAt_scalarCurve :
    HasDerivAt (fun s => toL (scalarCurve E a s).val) (oneL E a) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  rw [hasDerivAt_pi]
  intro w
  by_cases h : i = j
  · subst h
    have e : (fun s : ℝ => toL (scalarCurve E a s).val i i w) = fun s : ℝ => Complex.exp (s : ℂ) := by
      funext s
      simp [scalarCurve, toL, expU, Matrix.scalar_apply]
    have d : HasDerivAt (fun s : ℝ => Complex.exp (s : ℂ)) 1 0 := by
      simpa using (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
    have o : oneL E a i i w = 1 := by simp [oneL, toL]
    rw [e, o]
    exact d
  · have e : (fun s : ℝ => toL (scalarCurve E a s).val i j w) = fun _ : ℝ => 0 := by
      funext s
      simp [scalarCurve, toL, Matrix.scalar_apply, h]
    have o : oneL E a i j w = 0 := by simp [oneL, toL, h]
    rw [e, o]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem eigen_along_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (c : ℂ),
    lie E a (oneL E a) φ = c • φ → ∀ (t : ℝ) (g : GA E a),
      φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  intro E _ _ _ a φ c hφ t g
  set f : ℝ → ℂ := fun u => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) with hf
  have hd : ∀ u, HasDerivAt f (c * f u) u := by
    intro u
    have h1 := hasDerivAt_curve φ (g * GlobalTheory.UnitaryBC.splitCentre E a u) (scalarCurve E a) (oneL E a)
      scalarCurve_zero hasDerivAt_scalarCurve
    have h2 : lieD (oneL E a) φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) = c * f u := by
      have := congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) hφ
      simpa [hf] using this
    rw [h2] at h1
    have h3 : HasDerivAt (fun x : ℝ => φ.1 ((g * GlobalTheory.UnitaryBC.splitCentre E a u) * infGL E a (scalarCurve E a (x - u))))
        (c * f u) u := by
      have h0 : u - u = (0 : ℝ) := sub_self u
      exact HasDerivAt.comp_sub_const u u (by rw [h0]; exact h1)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    have e : GlobalTheory.UnitaryBC.splitCentre E a x =
        GlobalTheory.UnitaryBC.splitCentre E a u * infGL E a (scalarCurve E a (x - u)) := by
      have := GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add (E := E) (a := a) u (x - u)
      rw [add_sub_cancel] at this
      exact this
    simp only [hf, e, mul_assoc]
  have hP : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-c * v) * f v)
      (Complex.exp (-c * u) * (-c) * f u + Complex.exp (-c * u) * (c * f u)) u := by
    intro u
    have h0 : HasDerivAt (fun v : ℝ => -c * (v : ℂ)) (-c) u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-c)
    exact h0.cexp.mul (hd u)
  have hconst : ∀ u : ℝ, Complex.exp (-c * u) * f u = Complex.exp (-c * (0 : ℝ)) * f 0 := by
    refine fun u => is_const_of_deriv_eq_zero (f := fun v : ℝ => Complex.exp (-c * v) * f v)
      (fun x => (hP x).differentiableAt) (fun x => ?_) u 0
    rw [(hP x).deriv]
    ring
  have h0 : f 0 = φ.1 g := by
    simp [hf, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero]
  have ht := hconst t
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0] at ht
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm]
  change f t = _
  rw [← ht, ← mul_assoc, ← Complex.exp_add]
  simp

end GlobalTheory.CompanionTheory.Clozel

end
