import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory Filter GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.zero_pf :
    AeEq → Zero := by
  intro hAe E _ _ _ n D f I hf hinv hI h
  classical
  haveI : T2Space (H E n 0) := (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D).t2
  haveI : LocallyCompactSpace (H E n 0) := (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D).lc
  haveI : SecondCountableTopology (H E n 0) := (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D).sc
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  have key : ∀ K : Set (H E n 0), IsCompact K → ∀ᵐ x ∂D.ν, x ∈ K → ldet x ∈ I → f x = 0 := by
    intro K hK
    set S : Set (H E n 0) := K ∩ ldet ⁻¹' I with hS
    have hSm : MeasurableSet S :=
      hK.isClosed.measurableSet.inter (hI.preimage continuous_ldet).measurableSet
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
    have hνS : D.ν S < ⊤ :=
      lt_of_le_of_lt ((Measure.restrict_apply_le _ _).trans (measure_mono Set.inter_subset_left))
        (hK.measure_lt_top_of_nhdsWithin fun x _ => D.μ.finiteAt_nhdsWithin x K)
    set w : H E n 0 → ℂ := S.indicator fun x => starRingEnd ℂ (f x) with hwdef
    have hw : MemLp w 2 D.ν := by
      rw [hwdef, memLp_indicator_iff_restrict hSm]
      haveI : IsFiniteMeasure (D.ν.restrict S) := isFiniteMeasure_restrict.2 hνS.ne
      refine MemLp.of_bound (Complex.continuous_conj.comp hf).aestronglyMeasurable B
        ((ae_restrict_iff' hSm).2 (Eventually.of_forall fun x hx => ?_))
      simpa using hB x hx.1
    have hv : (hw.toLp w : H E n 0 → ℂ) =ᵐ[D.ν] w := hw.coeFn_toLp
    have h0 := h (hw.toLp w) (hv.mono fun y hy hl => by
      rw [hy]
      exact Set.indicator_of_notMem (fun hs => hl hs.2) _)
    have hpt : ∀ y, w y * f y = ((‖w y‖ ^ 2 : ℝ) : ℂ) := by
      intro y
      by_cases hy : y ∈ S
      · simp only [hwdef, Set.indicator_of_mem hy, RCLike.norm_conj]
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · simp [hwdef, Set.indicator_of_notMem hy]
    have h1 : ∫ y, ‖w y‖ ^ 2 ∂D.ν = 0 := by
      have e : ∫ y, (hw.toLp w : H E n 0 → ℂ) y * f y ∂D.ν = ∫ y, ((‖w y‖ ^ 2 : ℝ) : ℂ) ∂D.ν :=
        integral_congr_ae (hv.mono fun y hy => by
          show (hw.toLp w : H E n 0 → ℂ) y * f y = ((‖w y‖ ^ 2 : ℝ) : ℂ)
          rw [hy, hpt])
      rw [e, integral_complex_ofReal] at h0
      exact_mod_cast h0
    have hint : Integrable (fun y => ‖w y‖ ^ 2) D.ν := hw.integrable_norm_pow two_ne_zero
    have h2 := (integral_eq_zero_iff_of_nonneg (fun y => by positivity) hint).1 h1
    refine h2.mono fun x hx hxK hxI => ?_
    have hx0 : w x = 0 := by simpa using hx
    have hxS : x ∈ S := ⟨hxK, hxI⟩
    rw [hwdef, Set.indicator_of_mem hxS] at hx0
    simpa using hx0
  have all : ∀ᵐ x ∂D.ν, ∀ m : ℕ, x ∈ compactCovering (H E n 0) m → ldet x ∈ I → f x = 0 :=
    ae_all_iff.2 fun m => key _ (isCompact_compactCovering _ m)
  refine hAe E n D f (fun _ => 0) I hf continuous_const hinv (fun _ _ => rfl) hI (all.mono fun x hx hl => ?_)
  obtain ⟨m, hm⟩ := exists_mem_compactCovering x
  exact hx m hm hl
