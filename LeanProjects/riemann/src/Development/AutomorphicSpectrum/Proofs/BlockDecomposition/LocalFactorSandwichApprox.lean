import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncSum
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.AdeleLC
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich

variable {F : Type} [Field F] [NumberField F]

def ballV (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Set (Fv F v) :=
  {y | Valued.v y ≤ WithZero.exp (-(n : ℤ))}

theorem isClopen_ballV (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : IsClopen (ballV v n) := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-(n : ℤ)))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : ballV v n = {y : Fv F v | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [ballV, Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isClopen_closedBall _ (by simp [hc0])

theorem ballV_subset (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ballV v n ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := by
  intro y hy
  have h1 : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 : Valued.v y ≤ 1 := le_trans (show Valued.v y ≤ _ from hy) h1
  exact h2

theorem antitone_ballV (v : HeightOneSpectrum (𝓞 F)) : Antitone (ballV (F := F) v) := by
  intro m n hmn y hy
  show Valued.v y ≤ _
  refine le_trans (show Valued.v y ≤ _ from hy) ?_
  rw [WithZero.exp_le_exp]
  omega

theorem iInter_ballV (v : HeightOneSpectrum (𝓞 F)) : ⋂ n, ballV (F := F) v n = {0} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hy
    have hv0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have h1 := h (-(Valued.v y).log + 1).toNat
    have h2 : Valued.v y ≤ WithZero.exp (-(((-(Valued.v y).log + 1).toNat : ℕ) : ℤ)) := h1
    conv_lhs at h2 => rw [← WithZero.exp_log hv0]
    rw [WithZero.exp_le_exp] at h2
    have := Int.self_le_toNat (-(Valued.v y).log + 1)
    omega
  · rintro rfl n
    simp [ballV]

theorem nhdsNE_Fv (v : HeightOneSpectrum (𝓞 F)) : (𝓝[≠] (0 : Fv F v)).NeBot := by
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

theorem tendsto_real_ballV {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (hstd : IsStdV v lam) :
    Tendsto (fun n => lam.real (ballV v n)) atTop (𝓝 0) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  haveI := nhdsNE_Fv v
  have hfin : ∀ n, lam (ballV v n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (by rw [hstd.2]; exact ENNReal.one_ne_top) (measure_mono (ballV_subset v n))
  have h := tendsto_measure_iInter_atTop (μ := lam) (s := ballV v)
    (fun n => (isClopen_ballV v n).isOpen.measurableSet.nullMeasurableSet) (antitone_ballV v) ⟨0, hfin 0⟩
  rw [iInter_ballV, measure_singleton] at h
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Measure.real, Function.comp_def] using h2

theorem exists_sandwich : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ), IsStdV v lam → (∀ s, 0 ≤ g s) → GoodFac v lam C g → ∀ η : ℝ, 0 < η → ∃ ψm ψp : Fv F v → ℝ, Continuous ψm ∧ HasCompactSupport ψm ∧ Continuous ψp ∧ HasCompactSupport ψp ∧ (∀ s, 0 ≤ ψm s) ∧ (∀ s, s ≠ 0 → ψm s ≤ g s ∧ g s ≤ ψp s) ∧ 1 - η ≤ ∫ s, ψm s ∂lam ∧ ∫ s, ψp s ∂lam ≤ 1 + η := by
  intro F _ _ v lam C g hstd hg0 hg η hη
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  haveI := nhdsNE_Fv v
  obtain ⟨hcont, hout, hint, -, hone⟩ := hg
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + |C| := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hgK : ∀ s, s ≠ 0 → g s ≤ K := by
    intro s hs
    by_cases hO : s ∈ v.adicCompletionIntegers F
    · have h1 := hint s hO hs
      have h2 : C / (Ideal.absNorm v.asIdeal : ℝ) ≤ |C| :=
        (div_le_self (abs_nonneg C) hq |>.trans' (div_le_div_of_nonneg_right (le_abs_self C) (by linarith)))
      have h3 := (abs_le.1 h1).2
      rw [hKdef]; linarith
    · rw [hout s hO]; exact hK0.le
  have hgi : Integrable g lam := by
    by_contra h
    rw [integral_undef h] at hone
    norm_num at hone
  have hnz : ∀ᵐ s ∂lam, s ≠ 0 := by
    have : ({0}ᶜ : Set (Fv F v)) ∈ ae lam := compl_mem_ae_iff.2 (measure_singleton 0)
    exact this
  have hlim : Tendsto (fun n => K * lam.real (ballV v n)) atTop (𝓝 0) := by
    simpa using (tendsto_real_ballV hstd).const_mul K
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  obtain ⟨B, hB⟩ : ∃ B, B = ballV v n := ⟨_, rfl⟩
  rw [← hB] at hn
  have hBc : IsClopen B := hB ▸ isClopen_ballV v n
  have hBO : B ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := hB ▸ ballV_subset v n
  have h0B : (0 : Fv F v) ∈ B := by rw [hB]; simp [ballV]
  have hBm : MeasurableSet B := hBc.isOpen.measurableSet
  have hBfin : lam B ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [hstd.2]; exact ENNReal.one_ne_top) (measure_mono hBO)
  have hcomp : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Formalism.L2.S.S7.AdeleLC.isCompact_integers v
  have hψm : Continuous (Bᶜ.indicator g) := by
    refine continuous_indicator ?_ ?_
    · intro a ha
      rw [hBc.compl.frontier_eq] at ha
      exact absurd ha (Set.notMem_empty a)
    · rw [hBc.compl.isClosed.closure_eq]
      refine hcont.mono ?_
      intro s hs h0
      exact hs (by rw [Set.mem_singleton_iff.1 h0]; exact h0B)
  have hψb : Continuous (B.indicator fun _ => K) :=
    by
    refine continuous_indicator ?_ continuous_const.continuousOn
    intro a ha
    rw [hBc.frontier_eq] at ha
    exact absurd ha (Set.notMem_empty a)
  have hIm : ∫ s, Bᶜ.indicator g s ∂lam = ∫ s in Bᶜ, g s ∂lam := integral_indicator hBm.compl
  have hsplit : ∫ s in B, g s ∂lam + ∫ s in Bᶜ, g s ∂lam = 1 := by
    rw [integral_add_compl hBm hgi, hone]
  have hpos : 0 ≤ ∫ s in B, g s ∂lam := setIntegral_nonneg hBm fun s _ => hg0 s
  have hconst : ∫ s in B, K ∂lam = K * lam.real B := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hup : ∫ s in B, g s ∂lam ≤ K * lam.real B := by
    rw [← hconst]
    refine integral_mono_ae hgi.integrableOn (integrableOn_const hBfin) ?_
    exact ae_restrict_of_ae (hnz.mono fun s hs => hgK s hs)
  have hi1 : Integrable (Bᶜ.indicator g) lam := hgi.indicator hBm.compl
  have hi2 : Integrable (B.indicator fun _ => K) lam :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hBfin)
  have hIp : ∫ s, (Bᶜ.indicator g s + B.indicator (fun _ => K) s) ∂lam =
      ∫ s in Bᶜ, g s ∂lam + K * lam.real B := by
    rw [integral_add hi1 hi2, hIm, integral_indicator hBm, hconst]
  refine ⟨Bᶜ.indicator g, fun s => Bᶜ.indicator g s + B.indicator (fun _ => K) s, hψm, ?_,
    hψm.add hψb, ?_, fun s => Set.indicator_nonneg (fun s _ => hg0 s) s, ?_, ?_, ?_⟩
  · refine HasCompactSupport.intro hcomp fun s hs => ?_
    simp [Set.indicator, hout s hs]
  · refine HasCompactSupport.intro hcomp fun s hs => ?_
    have hsB : s ∉ B := fun h => hs (hBO h)
    simp [hsB, hout s hs]
  · intro s hs
    by_cases hsB : s ∈ B
    · simp only [Set.indicator, Set.mem_compl_iff, hsB, not_true_eq_false, if_false, if_true, zero_add]
      exact ⟨hg0 s, hgK s hs⟩
    · simp [Set.indicator, hsB]
  · rw [hIm]; linarith
  · rw [hIp]; linarith

end GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich

end
