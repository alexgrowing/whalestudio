import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

private theorem test_trM (D : Dom E n 0) {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ) :
    IsTestH (trM Φ M) := by
  have h := (kerLin (ctx ratProper_holds D) (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1)
    (fun p => hΦ p.1 p.2)).1
  have e : trM Φ M = fun z => ∑ p : ι × ι, Φ p.1 p.2 z * M p.2 p.1 := by
    funext z
    simp only [trM, Fintype.sum_prod_type]
  rw [e]
  exact h

private theorem measurable_cnt (D : Dom E n 0) {Ω : Set (H E n 0)} (hΩ : IsCompact Ω) :
    Measurable (cnt (ratH E n 0) Ω) := by
  haveI : T2Space (H E n 0) := (ctx ratProper_holds D).t2
  haveI : IsTopologicalGroup (H E n 0) := (ctx ratProper_holds D).tg
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI : Countable (ratH E n 0) := Dcy.countable_ratH'
  unfold cnt
  refine Measurable.ennreal_tsum fun γ => ?_
  have hc : Continuous fun x : H E n 0 => x⁻¹ * (γ : H E n 0) * x :=
    (continuous_inv.mul continuous_const).mul continuous_id
  exact (measurable_one.indicator hΩ.isClosed.measurableSet).comp hc.measurable

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.halfTerm_pf :
    Basic → GBound → Supp → Rep → Flip → DomInt → HalfTerm := by
  intro hB hGB hSu hRep hFl hDI E _ _ _ n ι _ s m ψ hψ x₀ hx₀
  classical
  haveI : T2Space (H E n 0) := (ctx ratProper_holds s.D).t2
  haveI : SecondCountableTopology (H E n 0) := (ctx ratProper_holds s.D).sc
  haveI : IsTopologicalGroup (H E n 0) := (ctx ratProper_holds s.D).tg
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI : IsLocallyFiniteMeasure s.D.μ := s.D.haar.2.2.2
  haveI : SFinite s.D.ν := by unfold Dom.ν; infer_instance
  obtain ⟨hlac, hlmul, -, -, -, hacc, -, -, -, -, hlc, hthc⟩ := hB E n s.pos
  have hφ : IsTestH m.φ := test_trM s.D m.t s.M
  have hψc : Continuous ψ.1 := continuous_of_mem s.π hψ
  obtain ⟨R₀, hR₀⟩ := (hφ.2.isCompact).exists_bound_of_continuousOn hlc.continuousOn
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ z, m.φ z ≠ 0 → |ldet z| ≤ R := fun z hz =>
    (hR₀ z (subset_tsupport _ hz)).trans (le_max_left _ _)
  obtain ⟨Ω, hΩ, hG⟩ := hGB E n ι s
  obtain ⟨C, hC0, hCb⟩ := hG x₀
  obtain ⟨N, hN⟩ := hDI E n s.pos s.D s.π s.fix ψ hψ Ω hΩ
  obtain ⟨C', hC', hb⟩ := hN 0 le_rfl
  have hb' := hb (R + 1) 0 (by positivity)
  have hcf : ∀ x, cnt (ratH E n 0) Ω x ≠ ⊤ := (cntBasic (ctx ratProper_holds s.D)).1 Ω hΩ
  have hcm := measurable_cnt s.D hΩ
  have hA : 0 ≤ C * ‖m.U‖ := mul_nonneg hC0 (norm_nonneg _)
  set S : Set (H E n 0) := {x | |ldet x| ≤ R + 1} with hS
  have hSm : MeasurableSet S := (isClosed_le (continuous_abs.comp hlc) continuous_const).measurableSet
  let F : ℝ → H E n 0 → ℂ := fun t x => ψ.1 x.1 * m.G (ac E n t * x₀) x
  let mm : H E n 0 → ℂ := fun z => m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1))
  let d : H E n 0 → ℝ := S.indicator fun x => ‖ψ.1 x.1‖ * (C * ‖m.U‖) * (cnt (ratH E n 0) Ω x).toReal
  have hlm : Measurable (ldet : H E n 0 → ℝ) := hlc.measurable

  have hFj : Continuous (Function.uncurry F) := by
    refine (hψc.comp (continuous_fst.comp continuous_snd)).mul ?_
    refine continuous_finset_sum _ fun i _ => ?_
    refine Continuous.inner ?_ ?_
    · exact (s.vecs.cont i).1.comp ((hacc.comp continuous_fst).mul continuous_const)
    · exact m.Uπ.continuous.comp ((s.vecs.cont i).2.comp continuous_snd)
  have hFs : ∀ x, Continuous fun t => F t x := fun x =>
    hFj.comp (continuous_id.prodMk continuous_const)

  have hmm : Integrable mm s.D.μ := by
    haveI : IsFiniteMeasureOnCompacts s.D.μ :=
      ⟨fun K hK => hK.measure_lt_top_of_nhdsWithin fun x _ => s.D.μ.finiteAt_nhdsWithin x K⟩
    refine Continuous.integrable_of_hasCompactSupport ?_ hφ.2.mul_right
    refine hφ.1.mul (hψc.comp ?_)
    have : Continuous fun z : H E n 0 => (th (x₀ * z)).1 :=
      continuous_fst.comp (hthc.comp (continuous_const.mul continuous_id))
    exact this

  have hdm : Measurable d := by
    refine Measurable.indicator ?_ hSm
    refine Measurable.mul ?_ hcm.ennreal_toReal
    exact ((hψc.comp continuous_fst).norm.mul continuous_const).measurable
  have hdI : Integrable d s.D.ν := by
    refine ⟨hdm.aestronglyMeasurable, ?_⟩
    set f : H E n 0 → ℝ≥0∞ := {x | |ldet x| ≤ R + 1 ∧ (0 : ℝ) ≤ r0 x}.indicator
      (fun x => ‖ψ.1 x.1‖ₑ * cnt (ratH E n 0) Ω x) with hf
    have hpt : ∀ x, ‖d x‖ₑ ≤ ENNReal.ofReal (C * ‖m.U‖) * f x := by
      intro x
      by_cases hx : x ∈ S
      · have hx' : x ∈ {x | |ldet x| ≤ R + 1 ∧ (0 : ℝ) ≤ r0 x} := ⟨hx, Dcy.redSize_nonneg _⟩
        have e1 : d x = ‖ψ.1 x.1‖ * (C * ‖m.U‖) * (cnt (ratH E n 0) Ω x).toReal :=
          Set.indicator_of_mem hx _
        rw [e1, hf, Set.indicator_of_mem hx', Real.enorm_eq_ofReal (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
          ENNReal.ofReal_toReal (hcf x)]
        exact le_of_eq (by ring)
      · have e1 : d x = 0 := Set.indicator_of_notMem hx _
        simp [e1]
    calc ∫⁻ x, ‖d x‖ₑ ∂s.D.ν ≤ ∫⁻ x, ENNReal.ofReal (C * ‖m.U‖) * f x ∂s.D.ν := lintegral_mono hpt
      _ = ENNReal.ofReal (C * ‖m.U‖) * ∫⁻ x, f x ∂s.D.ν := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt hb' ENNReal.ofReal_lt_top)

  have hlx : ∀ t, ldet (ac E n t * x₀) = t := fun t => by rw [hlmul, hlac, hx₀, add_zero]
  have hbd : ∀ t x, |t - ldet x| ≤ 1 → ‖F t x‖ ≤ d x := by
    intro t x htx
    by_cases hx : x ∈ S
    · have e1 : d x = ‖ψ.1 x.1‖ * (C * ‖m.U‖) * (cnt (ratH E n 0) Ω x).toReal :=
        Set.indicator_of_mem hx _
      rw [e1, mul_assoc]
      show ‖ψ.1 x.1 * m.G (ac E n t * x₀) x‖ ≤ _
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hcf x)) (hCb m t x)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] at h1
      simpa using h1
    · have e1 : d x = 0 := Set.indicator_of_notMem hx _
      have hx2 : R + 1 < |ldet x| := not_le.1 hx
      have hg : m.G (ac E n t * x₀) x = 0 := by
        refine hSu E n ι s m R hR _ _ ?_
        rw [hlx]
        by_contra hc
        have h1 := abs_le.1 (not_lt.1 hc)
        have h2 := abs_le.1 htx
        have h3 : |ldet x| ≤ R + 1 := abs_le.2 ⟨by linarith [h1.1, h1.2, h2.1, h2.2, hR0], by linarith [h1.1, h1.2, h2.1, h2.2, hR0]⟩
        exact hx h3
      rw [e1]
      show ‖ψ.1 x.1 * m.G (ac E n t * x₀) x‖ ≤ 0
      simp [hg]

  obtain ⟨ψ', hψ', hθ⟩ := s.fix.2 ψ hψ
  have hrep : ∀ (t : ℝ) (u : ℝ → ℂ), Continuous u → HasCompactSupport u →
      ∫ x, F t x * u (ldet x) ∂s.D.ν = ∫ z, mm z * u (-(t + ldet z)) ∂s.D.μ := by
    intro t u hu hu'
    have h := (hRep E n ι s m ψ hψ u hu hu' (ac E n t * x₀)).2
    refine h.trans (integral_congr_ae (Eventually.of_forall fun z => ?_))
    show m.φ z * ψ.1 (thetaA E n ((ac E n t * x₀).1 * z.1)) * u (-(ldet (ac E n t * x₀) + ldet z)) =
      m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1)) * u (-(t + ldet z))
    have e : (ac E n t * x₀).1 * z.1 = splitCentre E n (t / (n * Module.finrank ℚ E)) * (x₀.1 * z.1) := by
      simp only [ac, Prod.fst_mul, mul_assoc]
    rw [hlx, e, ← hθ, ← hθ, s.fix.1 ψ' hψ']
  exact hFl (H E n 0) (H E n 0) s.D.ν s.D.μ ldet ldet F mm d hlm hlm hFj.measurable hFs hmm hdI hbd hrep
