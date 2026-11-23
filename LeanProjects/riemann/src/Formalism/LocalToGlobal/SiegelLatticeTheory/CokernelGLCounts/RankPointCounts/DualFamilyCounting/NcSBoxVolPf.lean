import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSBoxSteps

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.BoxVolPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open Formalism.L2.SG.Pf.NcS.BoxVolSk Formalism.L2.SG.Pf.NcS.BoxSteps Formalism.L2.SG.Pf.NcS.FinVolSk
open scoped TensorProduct

theorem finprod_box {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n a d : ℕ} (b : Module.Basis (Fin d) F E)
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E))
    (hCa : ∀ᶠ v in Filter.cofinite, C v = latV b v) (x : Fin a → Fin n → Af F ⊗[F] E) :
    (∏ᶠ v, (C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v x)) =
      ({x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v}.indicator 1 x : ℂ) := by
  classical
  have hev : ∀ᶠ v in Filter.cofinite, projV v x ∈ C v := by
    filter_upwards [finite_integral_holds F E n a d b x, hCa] with v h1 h2
    rw [h2]; exact h1
  have hfin : (Function.mulSupport fun v =>
      (C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v x)).Finite := by
    refine (Filter.eventually_cofinite.1 hev).subset fun v hv => ?_
    intro hm
    apply hv
    simp [Set.indicator_of_mem hm]
  by_cases hx : ∀ v, projV v x ∈ C v
  · rw [Set.indicator_of_mem (show x ∈ {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v} from hx)]
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    simp [Set.indicator_of_mem (hx v)]
  · rw [Set.indicator_of_notMem (show x ∉ {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v} from hx)]
    push Not at hx
    obtain ⟨v0, hv0⟩ := hx
    exact finprod_eq_zero _ v0 (Set.indicator_of_notMem hv0 _) hfin

theorem box_volume_holds : BoxVol := by
  intro F E _ _ _ _ _ σ n J ψ a X0 hT νX hStd hdet ha hn hSWa hSWc hOm μinf νinf fibInf hμ hν hfib hne
    ωf hdec
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set TI := hermOf (Ainf F) σ (gramE σ J X0) hT with hTI
  obtain ⟨Φi, hΦc, hΦs, hΦ0, hΦint, hΦpos⟩ := positivity_test_holds F E σ n J a μinf νinf fibInf TI hfib hne
  set c : ENNReal := ∫⁻ z, ENNReal.ofReal (Φi z) ∂(fibInf TI) with hcdef
  have hc : c = ENNReal.ofReal (∫ z, Φi z ∂(fibInf TI)) :=
    (ofReal_integral_eq_lintegral_ofReal hΦint (Filter.Eventually.of_forall hΦ0)).symm
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 hΦpos).ne'
  have hcT : c ≠ ⊤ := by rw [hc]; exact ENNReal.ofReal_ne_top
  obtain ⟨hGm, hGf, hGv⟩ := gram_measurable_holds F E σ n J a (gramE σ J X0)
  have hae : ∀ᵐ y ∂νX, gramR (AF F) σ J y = (gramE σ J X0).map (inclR (AF F)) := by
    rw [Filter.Eventually, mem_ae_iff]
    simpa [Set.compl_ofPred] using hOm.1
  refine ⟨?_, ?_⟩
  · set S := {x : Fin a → Fin n → Af F ⊗[F] E | gramR (Af F) σ J x ≠ (gramE σ J X0).map (inclR (Af F))}
      with hSdef
    have h1 := hdec (fun z => ENNReal.ofReal (Φi z)) S hGm
    have hL : ∫⁻ y, ENNReal.ofReal (Φi (projInf y)) * S.indicator 1 (projFin y) ∂νX = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
      filter_upwards [hae] with y hy
      have : projFin y ∉ S := fun h => h (hGf y hy)
      simp [Set.indicator_of_notMem this]
    rw [hL] at h1
    have hS0 : ωf S = 0 := by
      rcases (mul_eq_zero.1 h1.symm) with h | h
      · exact h
      · exact absurd h hc0
    refine measure_mono_null (fun x hx => ?_) hS0
    intro hxT
    exact hx (hGv x hxT)
  · intro d b C hSB hCm hCa
    set B := {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v} with hBdef
    have hBm : MeasurableSet B := box_measurable_holds F E n a C hCm
    have h2 := hdec (fun z => ENNReal.ofReal (Φi z)) B hBm

    have hA1 := hOm.2.2 μinf hμ
    have hA2 := hA1.2 νinf hν
    have hdX : ∀ v, SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a) := by
      intro v
      obtain ⟨μv, hμv⟩ := hA2.1
      have hex : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ := ⟨μv v, hμv v⟩
      simp only [dX, dif_pos hex]
      exact hex.choose_spec
    have hA3 := hA2.2 (fun v => dX σ J ψ v a) hdX
    have hdT : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (dT σ ψ v a) := by
      intro v
      obtain ⟨νv, hνv⟩ := hA3.1
      have hex : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν := ⟨νv v, hνv v⟩
      simp only [dT, dif_pos hex]
      exact hex.choose_spec
    have hA4 := hA3.2 (fun v => dT σ ψ v a) hdT
    have hA5 := hA4.2 fibInf hfib
    have hOmF : ∀ v, IsOm σ J ψ v a (omFam σ J ψ v a) := by
      intro v
      obtain ⟨fibV, hfibV⟩ := hA5.1
      have hex : ∃ fib, IsOm σ J ψ v a fib := ⟨fibV v, hfibV v⟩
      simp only [omFam, dif_pos hex]
      exact hex.choose_spec
    have hQ := hA5.2 (fun v => omFam σ J ψ v a) hOmF

    let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ :=
      fun v => (C v).indicator 1
    let Φf : (Fin a → Fin n → Af F ⊗[F] E) → ℂ := fun x => ∏ᶠ v, Φv v (projV v x)
    let Φinf : (Fin a → Fin n → Ainf F ⊗[F] E) → ℂ := fun z => (Φi z : ℂ)
    let Φ : (Fin a → Fin n → AF F ⊗[F] E) → ℂ := fun y => Φinf (projInf y) * Φf (projFin y)
    have hpure : IsPureFin b Φf Φv :=
      ⟨hSB, hCa.mono fun v h => by simp only [Φv, h], fun X => rfl⟩
    obtain ⟨hInt, hMult, hEq⟩ := hQ d b Φ Φinf Φf Φv (Complex.continuous_ofReal.comp hΦc)
      (hΦs.comp_left Complex.ofReal_zero) hpure (fun X => rfl)

    let g : (Fin a → Fin n → AF F ⊗[F] E) → ℝ := fun y => Φi (projInf y) * B.indicator 1 (projFin y)
    have hΦg : ∀ y, Φ y = (g y : ℂ) := by
      intro y
      simp only [Φ, Φinf, Φf, Φv, g]
      rw [finprod_box b C hCa (projFin y), ← hBdef]
      by_cases hy : projFin y ∈ B
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    have hg0 : ∀ y, 0 ≤ g y := fun y => mul_nonneg (hΦ0 _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hgInt : Integrable g νX := by
      have : Integrable (fun y => (g y : ℂ)) νX := hInt.congr (Filter.Eventually.of_forall hΦg)
      exact this.re
    have hlin : ∫⁻ y, ENNReal.ofReal (g y) ∂νX =
        ∫⁻ y, ENNReal.ofReal (Φi (projInf y)) * B.indicator 1 (projFin y) ∂νX := by
      refine lintegral_congr fun y => ?_
      by_cases hy : projFin y ∈ B
      · simp [g, Set.indicator_of_mem hy]
      · simp [g, Set.indicator_of_notMem hy]
    have hLHS : ∫ y, Φ y ∂νX = ((ωf B * c).toReal : ℂ) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hΦg), integral_complex_ofReal,
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hgInt.aestronglyMeasurable,
        hlin, h2]
    have hfinB : ωf B * c ≠ ⊤ := by
      rw [← h2, ← hlin]; exact (hgInt.lintegral_lt_top).ne
    have hωT : ωf B ≠ ⊤ := by
      intro h; apply hfinB; rw [h]; exact ENNReal.top_mul hc0

    have hloc : ∀ v, (∫ X, Φv v X ∂(omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT))) =
        (((omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v))))
          (C v ∩ {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))})).toReal : ℂ) := by
      intro v
      have hom : omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v))) =
          omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT) := by
        simp only [omAt, dif_pos (map_mem_HermR (Fv F v) σ (gramE σ J X0) hT)]
        rfl
      have hnull : omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT)
          {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))}ᶜ = 0 :=
        measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) ((hOmF v).1 _)
      rw [hom, measure_inter_conull hnull]
      have e : Φv v = fun X => (((C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℝ) X : ℝ) : ℂ) := by
        funext X
        by_cases hX : X ∈ C v
        · simp [Φv, Set.indicator_of_mem hX]
        · simp [Φv, Set.indicator_of_notMem hX]
      rw [e, integral_complex_ofReal, integral_indicator_one (hCm v), Measure.real]
    let r : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
      ((omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v))))
        (C v ∩ {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))})).toReal
    have hMult' : Multipliable (fun v => (r v : ℂ)) := by
      have : (fun v => ∫ X, Φv v X ∂(omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT))) =
        fun v => (r v : ℂ) := funext hloc
      rw [← this]; exact hMult
    have hRHS : (∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) *
        ∏' v, ∫ X, Φv v X ∂(omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
        (((∫ z, Φi z ∂(fibInf TI)) * ∏' v, r v : ℝ) : ℂ) := by
      rw [tprod_congr hloc, BoxVolSk_tprod_ofReal r hMult']
      simp only [Φinf]
      rw [integral_complex_ofReal, Complex.ofReal_mul]
    rw [hLHS, hRHS, Complex.ofReal_inj, ENNReal.toReal_mul] at hEq
    have hcR : c.toReal = ∫ z, Φi z ∂(fibInf TI) := by
      rw [hc, ENNReal.toReal_ofReal (integral_nonneg hΦ0)]
    rw [hcR, mul_comm] at hEq
    have hB : (ωf B).toReal = ∏' v, r v := mul_left_cancel₀ hΦpos.ne' hEq
    rw [← hB, ENNReal.ofReal_toReal hωT]

end Formalism.L2.SG.Pf.NcS.BoxVolPf
