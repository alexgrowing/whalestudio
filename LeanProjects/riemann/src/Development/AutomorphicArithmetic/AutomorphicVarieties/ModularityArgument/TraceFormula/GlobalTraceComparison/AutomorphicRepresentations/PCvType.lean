import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private lemma shiftInt (D : Dom E n 0) (a : H E n 0) (F : H E n 0 → ℂ) :
    ∫ y, F (a * y) ∂D.μ = ∫ y, F y ∂D.μ := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI := D.haar.1
  exact integral_mul_left_eq_self F a

private lemma ldet_shift (a : GA E n) (h : logAbs a.val.det = 0) (y : H E n 0) :
    ldet (((a, 1) : H E n 0) * y) = ldet y := by
  simp only [ldet, Prod.fst_mul, DiscreteGroups.T1.G.Dcy.logAbs_det_mul', h, zero_add]

private lemma cv_shift (D : Dom E n 0) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ) (g a : GA E n)
    (h : logAbs a.val.det = 0) :
    cvF D.μ φ u f (g * a) = ∫ y, φ ((a⁻¹, 1) * y) * u (ldet y) * f (g * y.1) ∂D.μ := by
  rw [← shiftInt D ((a, 1) : H E n 0) (fun y => φ ((a⁻¹, 1) * y) * u (ldet y) * f (g * y.1))]
  unfold cvF
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have e : ((a⁻¹, 1) : H E n 0) * (((a, 1) : H E n 0) * y) = y := by
    rw [← mul_assoc]; simp
  simp only [e, ldet_shift a h, Prod.fst_mul, mul_assoc]

private lemma term_integrable (D : Dom E n 0) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ) (g a : GA E n)
    (hφ : IsTestH φ) (hu : Continuous u) (hf : Continuous f) :
    Integrable (fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1)) D.μ := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI := D.haar.2.2.2
  haveI : IsFiniteMeasureOnCompacts D.μ :=
    ⟨fun _ h => h.measure_lt_top_of_nhdsWithin fun x _ => D.μ.finiteAt_nhdsWithin x _⟩
  have c1 : Continuous fun y : H E n 0 => φ ((a, 1) * y) := hφ.1.comp (continuous_const.mul continuous_id)
  have s1 : HasCompactSupport fun y : H E n 0 => φ ((a, 1) * y) :=
    hφ.2.comp_homeomorph (Homeomorph.mulLeft ((a, 1) : H E n 0))
  have s3 : HasCompactSupport fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1) :=
    (s1.mul_right (f' := fun y : H E n 0 => u (ldet y))).mul_right (f' := fun y : H E n 0 => f (g * y.1))
  have c3 : Continuous fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1) :=
    (c1.mul (hu.comp DiscreteGroups.T1.G.continuous_ldet)).mul (hf.comp (continuous_const.mul continuous_fst))
  exact c3.integrable_of_hasCompactSupport s3

theorem cvType_pf : DetZero → EvalBasis → CvType := by
  intro hdz hev E _ _ _ n D K W φ u f hK hW hφ hL hu hf
  refine ⟨fun k hk g => ?_, fun g => ?_⟩
  · rw [cv_shift D φ u f g _ ((hdz E n).2 K hK k hk)]
    unfold cvF
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have := hL.1 k⁻¹ (K.inv_mem hk) y
    simp only [map_inv] at this
    simp only [this]
  · obtain ⟨d, x, w, hw, hs⟩ := hev (Kinf E n) (Kinf E n → ℂ) (fun x => LinearMap.proj x)
      (fun v hv => funext hv) W hW
    set c : Fin d → ℂ := fun b =>
      ∫ y, φ (((kI E n (x b))⁻¹, 1) * y) * u (ldet y) * f (g * y.1) ∂D.μ with hc
    have key : (fun k : Kinf E n => cvF D.μ φ u f (g * kI E n k)) = ∑ b, c b • w b := by
      funext k
      rw [cv_shift D φ u f g _ ((hdz E n).1 k)]
      have e : ∀ y : H E n 0, φ (((kI E n k)⁻¹, 1) * y) * u (ldet y) * f (g * y.1) =
          ∑ b, w b k * (φ (((kI E n (x b))⁻¹, 1) * y) * u (ldet y) * f (g * y.1)) := by
        intro y
        have := congrFun (hs _ (hL.2 y)) k
        simp only [LinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        rw [this, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      simp only [e]
      rw [integral_finset_sum _ fun b _ => (term_integrable D φ u f g _ hφ hu hf).const_mul _]
      simp only [integral_const_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [key]
    exact Submodule.sum_mem _ fun b _ => W.smul_mem _ (hw b)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
