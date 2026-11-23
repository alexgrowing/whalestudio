import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.PoincareLower

open Topology Filter

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem diff_fderiv_apply {F : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x) (a : E) :
    DifferentiableAt ℝ (fun v => fderiv ℝ F v a) x :=
  ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply (differentiableAt_const a)

theorem eventually_diff {F : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x) :
    ∀ᶠ v in 𝓝 x, DifferentiableAt ℝ F v :=
  (hF.eventually (by simp)).mono fun _ hv => hv.differentiableAt (by norm_num)

theorem fderiv_anti {F : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x) (a b c : E) :
    fderiv ℝ (fun v => (fderiv ℝ (fun u => (F u : ℂ)) v a + Complex.I * fderiv ℝ (fun u => (F u : ℂ)) v b) / 2) x c =
      ((fderiv ℝ (fun v => fderiv ℝ F v a) x c : ℝ) + Complex.I * (fderiv ℝ (fun v => fderiv ℝ F v b) x c : ℝ)) / 2 := by
  have e : (fun v => (fderiv ℝ (fun u => (F u : ℂ)) v a + Complex.I * fderiv ℝ (fun u => (F u : ℂ)) v b) / 2) =ᶠ[𝓝 x]
      fun v => (((fderiv ℝ F v a : ℝ) : ℂ) + Complex.I * ((fderiv ℝ F v b : ℝ) : ℂ)) * (2 : ℂ)⁻¹ := by
    filter_upwards [eventually_diff hF] with v hv
    have h : HasFDerivAt (fun u => (F u : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ F v)) v :=
      Complex.ofRealCLM.hasFDerivAt.comp v hv.hasFDerivAt
    rw [h.fderiv]
    simp [div_eq_mul_inv]
  have h1 : HasFDerivAt (fun v => ((fderiv ℝ F v a : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun v => fderiv ℝ F v a) x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (diff_fderiv_apply hF a).hasFDerivAt
  have h2 : HasFDerivAt (fun v => ((fderiv ℝ F v b : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun v => fderiv ℝ F v b) x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (diff_fderiv_apply hF b).hasFDerivAt
  rw [e.fderiv_eq, ((h1.fun_add (h2.const_mul Complex.I)).mul_const (2 : ℂ)⁻¹).fderiv]
  simp
  ring

end General

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domFlat : IsOpen (DomFlat ι p q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  refine Filter.eventually_all.2 fun τ => ExhB.posDef_eventually
    (fun v : ι × Fin p × Fin q → ℂ => 1 - (unflat v τ)ᴴ * unflat v τ) (fun i j => ?_)
    (fun v => isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)) x0 (hx0 τ)
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, unflat, Matrix.of_apply]
  fun_prop

theorem ddc_eq {f : Pt ι p q → ℝ} {z : Pt ι p q} (hf : ContDiffAt ℝ 2 (fun v => f (unflat v)) (flat z))
    (ξ : Pt ι p q) : ddc f z ξ =
      (fderiv ℝ (fun v => fderiv ℝ (fun u => f (unflat u)) v (flat ξ)) (flat z) (flat ξ) +
        fderiv ℝ (fun v => fderiv ℝ (fun u => f (unflat u)) v (flat (Complex.I • ξ))) (flat z)
          (flat (Complex.I • ξ))) / (4 * Real.pi) := by
  have e : ∀ ζ, dR (fun w => dAnti (fun u => (f u : ℂ)) w ξ) z ζ = _ :=
    fun ζ => fderiv_anti hf (flat ξ) (flat (Complex.I • ξ)) (flat ζ)
  rw [ddc, dHol, e, e]
  simp
  ring

variable {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (B : BdData ι p q Γ)

end GlobalTheory.PoincareLower
