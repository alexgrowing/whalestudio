import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.ProjRows
open scoped InnerProductSpace

namespace Formalism.L2.SG.EvalTRph

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem isFdeg_dv (v : InfinitePlace X.B.I.F) :
    IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.dv v) := by
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS (X.B.lam v) (X.B.σ v) (X.ds v)
  have hw : X.B.w v ≠ 0 := by
    intro h0
    have h1 := (X.low v).1
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have e : X.dv v = d := Formalism.MainNotions.DiscreteSeriesInnerProducts.fdegOf_eq hd hw
  rw [e]
  exact hd

theorem rph_fix_hom
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)))
    (Φ : X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund) (hΦ : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R) :
    X.Rph (Φ (X.B.tens X.B.w)) = Φ (X.B.tens X.B.w) := by
  apply ext_inner_left ℂ
  intro a
  have hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v) := fun v => (X.ds v).2.2.1
  have hw : ∀ v, ‖X.B.w v‖ = 1 := fun v => (X.low v).1
  have hs := (Formalism.L2.SG.Pf.glob_schur X.B.I X.B.σ X.dv X.B.w hU (isFdeg_dv X) hw hL X.B.σs X.B.tens
    X.B.tens_spec (ContinuousLinearMap.adjoint Φ a)).2
  rw [X.Rph_spec a (Φ (X.B.tens X.B.w))]
  have hg : ∀ g : X.B.I.Ginf, X.B.R (g, 1) (Φ (X.B.tens X.B.w)) = Φ (X.B.σs g (X.B.tens X.B.w)) := by
    intro g
    have := congrArg (fun L : X.B.Hs →L[ℂ] X.B.I.L2 X.B.μf X.B.fund => L (X.B.tens X.B.w)) (hΦ g)
    simpa using this.symm
  have hi : ∀ x : X.B.Hs, ⟪a, Φ x⟫_ℂ = ⟪ContinuousLinearMap.adjoint Φ a, x⟫_ℂ := fun x =>
    (ContinuousLinearMap.adjoint_inner_left Φ x a).symm
  rw [hi, ← hs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show _ * _ = _ * _
  rw [hg g, hi]
  rfl

theorem inner_tens_orbit (g : X.B.I.Ginf) :
    ⟪X.B.tens X.B.w, X.B.σs g (X.B.tens X.B.w)⟫_ℂ = mInf X.B.I X.B.σ X.B.w g := by
  rw [Formalism.L2.SG.Pf.orbit_eq X.B.I X.B.σ X.B.σs X.B.tens X.B.tens_spec X.B.w g, X.B.tens_spec.1]
  rfl

theorem inner_tens_self : ⟪X.B.tens X.B.w, X.B.tens X.B.w⟫_ℂ = 1 := by
  rw [X.B.tens_spec.1]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [inner_self_eq_norm_sq_to_K, (X.low v).1]
  simp

theorem integral_ph_m
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v))) :
    Integrable (fun g => X.ph g * mInf X.B.I X.B.σ X.B.w g) (muInf X.B.I) ∧
      ∫ g, X.ph g * mInf X.B.I X.B.σ X.B.w g ∂(muInf X.B.I) = 1 := by
  have hU : ∀ v, IsURepOn (UJset (X.B.I.ε v)) (X.B.σ v) := fun v => (X.ds v).2.2.1
  have hw : ∀ v, ‖X.B.w v‖ = 1 := fun v => (X.low v).1
  have hs := Formalism.L2.SG.Pf.glob_schur X.B.I X.B.σ X.dv X.B.w hU (isFdeg_dv X) hw hL X.B.σs X.B.tens
    X.B.tens_spec (X.B.tens X.B.w)
  simp_rw [inner_tens_orbit X] at hs
  rw [inner_tens_self X] at hs
  exact hs

theorem rph_isRowProj
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v))) :
    IsRowProj (fun g => X.B.R (g, 1)) (mInf X.B.I X.B.σ X.B.w) X.Rph :=
  Formalism.L2.SG.Closed.ProjRowsR_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec X.B.H X.B.σ X.dv X.B.w
    (fun v => (X.ds v).2.2.1) (isFdeg_dv X) (fun v => (X.low v).1) hL X.Rph X.Rph_spec

theorem rph_fix_of_coef
    (hL : ∀ v, Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)))
    (f : X.B.I.L2 X.B.μf X.B.fund)
    (hc : ∀ g : X.B.I.Ginf, ⟪f, X.B.R (g, 1) f⟫_ℂ = ((‖f‖ ^ 2 : ℝ) : ℂ) * mInf X.B.I X.B.σ X.B.w g) :
    X.Rph f = f := by
  have hP := rph_isRowProj X hL
  have h1 : ⟪f, X.Rph f⟫_ℂ = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [X.Rph_spec f f]
    have e : ∀ g, Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w
        (fun v => fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) g * ⟪f, X.B.R (g, 1) f⟫_ℂ =
        ((‖f‖ ^ 2 : ℝ) : ℂ) * (X.ph g * mInf X.B.I X.B.σ X.B.w g) := by
      intro g
      rw [hc g]
      show X.ph g * _ = _
      ring
    simp_rw [e]
    rw [integral_const_mul, (integral_ph_m X hL).2, mul_one]
  have h2 : ⟪X.Rph f, X.Rph f⟫_ℂ = ⟪f, X.Rph f⟫_ℂ := by
    rw [hP.1 f (X.Rph f)]
    congr 1
    exact congrArg (fun L : X.B.I.L2 X.B.μf X.B.fund →L[ℂ] X.B.I.L2 X.B.μf X.B.fund => L f) hP.2.1
  have h3 : ⟪X.Rph f, f⟫_ℂ = ⟪f, X.Rph f⟫_ℂ := hP.1 f f
  have h0 : ⟪f - X.Rph f, f - X.Rph f⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, h2, h3, h1, inner_self_eq_norm_sq_to_K]
    simp
  exact (sub_eq_zero.1 (inner_self_eq_zero.1 h0)).symm

end Formalism.L2.SG.EvalTRph

end
