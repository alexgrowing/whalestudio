import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetNotGG
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqSmulOfTwoSided
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreVolumeNormalFormStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymmStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoSidedSizeFunctionPosInvariantContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramNumberNormalizedInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagGramNumberNormalizedIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideUnfoldingStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.DegSide

variable {k r : ℕ}

theorem measurableSet_GG : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  simpa [Set.compl_setOf] using (WUnfold.measurableSet_not_GG (k := k) (r := r)).compl

theorem measurable_indicator_GG {β : Type} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [Zero β]
    {f : Mat k r → β} (hf : ContinuousOn f (GG k r)) :
    Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => f (Matrix.of x)) := by
  classical
  have h : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) {x : Mt k r | Matrix.of x ∈ GG k r} := hf
  have := h.measurable_piecewise (g := fun _ => (0 : β)) continuousOn_const measurableSet_GG
  rwa [← Set.piecewise_eq_indicator]

theorem measurable_mulP : Measurable fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := by
  have : Continuous fun p : Mat k r × Mat k r => p.1 * p.2 := continuous_fst.matrix_mul continuous_snd
  have h : Continuous fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := this
  exact h.measurable

theorem measurable_conjM (h : Mat k r) : Measurable (conjM h : Mt k r → Mt k r) := by
  have : Continuous fun x : Mat k r => h * x * h⁻¹ := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h' : Continuous (conjM h : Mt k r → Mt k r) := this
  exact h'.measurable

theorem null_of_fibres {z : Fin (2 * r + k + 1) → ℂ} {μG μW μN ν : Measure (Mt k r)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hW : IsHaarOn (UWset k r z) μW) (hN : IsHaarOn (Nset k r) μN) (hq : IsQuotMeas μG (muProd μW μN) ν)
    {A : Set (Mt k r)} (hA : MeasurableSet A) (h0 : ∀ g : Mat k r, μN (rmulM g ⁻¹' A) = 0) : μG A = 0 := by
  haveI := hN.1
  have hconj : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN :=
    (GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μW μN hz hT hW hN).2.2.2.2
  have hm : Measurable (A.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, hq _ hm]
  refine (lintegral_congr fun x => ?_).trans lintegral_zero
  have hx : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) s) :=
    hm.comp (continuous_rmulM _).measurable
  show ∫⁻ s, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) s) ∂(muProd μW μN) = 0
  unfold muProd
  rw [lintegral_map hx measurable_mulP, lintegral_prod (fun p : Mt k r × Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) (lmulM (Matrix.of p.1) p.2)))
      (hx.comp measurable_mulP).aemeasurable]
  have haeW : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := hW.2.2.1
  refine (lintegral_congr_ae (haeW.mono fun h hh => ?_)).trans lintegral_zero
  have hg : Measurable fun s : Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of h * Matrix.of x) s) :=
    hm.comp (continuous_rmulM _).measurable
  have e : ∀ n : Mt k r, rmulM (Matrix.of x) (lmulM (Matrix.of h) n) =
      rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n) := by
    intro n
    show (Matrix.of h * Matrix.of n * Matrix.of x : Mat k r) =
      Matrix.of h * Matrix.of n * (Matrix.of h)⁻¹ * (Matrix.of h * Matrix.of x)
    rw [Matrix.mul_assoc (Matrix.of h * Matrix.of n : Mat k r),
      Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hh.1)]
  show ∫⁻ n, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) (lmulM (Matrix.of h) n)) ∂μN = 0
  simp only [e]
  rw [← lintegral_map hg (measurable_conjM _), hconj _ hh, ← h0 (Matrix.of h * Matrix.of x),
    ← lintegral_indicator_one ((continuous_rmulM _).measurable hA)]
  rfl

theorem mem_Sset_of_mem_Nset (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, (isClosedSub_UWset z).2.2.1, n, hn, (Matrix.one_mul n).symm⟩

theorem Sg2_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {s x : Mat k r}
    (hs : s ∈ Sset k r z) (hx : x ∈ GG k r) : Sg2 k r z (s * x) = Sg2 k r z x := by
  have := (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z hz hT).2.1 x hx s hs 1 ⟨isClosedSub_GG.2.2.1, one_mem _⟩
  rwa [Matrix.mul_one] at this

theorem tail {Wq : Type} [NormedAddCommGroup Wq] {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {ν : Measure (Mt k r)} {Φ : Mat k r → Wq} {q : ℕ} {H₁ : ℝ} (hH : 1 ≤ H₁) (ht : TailBd z ν Φ q H₁) (i : ℕ)
    {Q : Set (Mt k r)} (hQ : MeasurableSet Q) (hsub : ∀ x ∈ Q, i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z (Matrix.of x)) :
    ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν ≤
      ENNReal.ofReal ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG ν Φ := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · refine (setLIntegral_le_lintegral _ _).trans (le_mul_of_one_le_left zero_le ?_)
    rw [ENNReal.one_le_ofReal]
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    simp only [pow_zero, one_pow, inv_one]
    linarith
  · have h2 : (0 : ℝ) < 2 ^ i := by positivity
    have h := ht (2 ^ i) h2
    have e : 2 * (2 * r + 2 : ℝ) * (2 ^ i : ℝ) ^ (-(2 * (q : ℝ))) = (4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹ := by
      rw [Real.rpow_neg h2.le, ← Real.rpow_natCast (2 ^ i : ℝ) (2 * q)]
      push_cast
      ring
    rw [e] at h
    refine le_trans ?_ h
    rw [← lintegral_indicator hQ]
    refine lintegral_mono (Set.indicator_le_indicator_of_subset (fun x hx => ?_) fun _ => zero_le)
    have hx' := (hsub x hx).resolve_left hi.ne'
    have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
    rcases ((GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z hz hT).2.2.2 (Matrix.of x)).2.2.2 with h' | ⟨a, ha⟩
    · exfalso
      rw [h'] at hx'
      nlinarith
    · exact ⟨a, ha ▸ hx'.le⟩

theorem side_bound : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ' : Mat k r → ℂ) (μG μW' νS' μR νR : Measure (Mt k r)) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → νR {x | Matrix.of x ∉ GG k r ∨ Yj k r hj z z' γ (Matrix.of x) = 0} = 0 ∧ ∀ w : Wq, ‖w‖ = 1 → ∀ (i : ℕ) (R₀ y : ℝ), 1 ≤ R₀ → 0 < y → ∫⁻ x in Eset0 k r hj z z' γ R₀ y ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)}, ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR ≤ ENNReal.ofReal (κ / s * fibVol0 k r j R₀ De y * ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * c) := by
  intro k r j hj z z' Wq _ _ _ π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hj1 hjk hκ hs hH hO ht hDe hNR hqR
  have hO' := hO
  obtain ⟨hz', hT', hnt, hπ, -, hG, hW, -, hN, hqS, hψ, hΦ, hΦc, hc, hl2⟩ := hO'
  have hz := hNR.1
  have hT := hNR.2.2.1
  obtain ⟨hγ, hRc, hRh, hRu, -⟩ := GlobalTheory.T.stabilizer_measure_normalisation_symm k r j hj z z' γ s μR hs hNR
  obtain ⟨hoff, hnull, φ, hφ, hcut⟩ := GlobalTheory.T.cutoff_computes_besselQuotientIntegral k r _ μG μR νR hRc hG hRh hRu hqR
  have hV := GlobalTheory.T.fibreVolume_normalFormStabiliser k r j hj z z' γ De s μR hj1 hjk hDe hs hNR
  obtain ⟨hYm, hEm⟩ := GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z z' γ hz hz' hT hT' hγ
  have hYi : ∀ ρ ∈ Rset k r γ, ∀ x ∈ GG k r, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x :=
    fun ρ hρ x hx => (GlobalTheory.T.flagGramNumberNormalized_invariance k r j hj z z' γ hz hz' hγ x hx).2.2 ρ hρ
  have hmul : ∀ a ∈ GG k r, ∀ b ∈ GG k r, a * b ∈ GG k r := isClosedSub_GG.2.2.2.1
  refine ⟨?_, fun w hw i R₀ y hR hy => ?_⟩
  · set A : Set (Mt k r) := {x | Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (Matrix.of x) = 0} with hAdef
    have hA : MeasurableSet A := by
      have := measurableSet_GG.inter (hYm (measurableSet_singleton 0))
      convert this using 1
      ext x
      refine and_congr_right fun hx => ?_
      rw [Set.mem_preimage, Set.indicator_of_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) (a := x) hx]
      rfl
    have hA0 : μG A = 0 := by
      refine null_of_fibres hz' hT' hW hN hqS hA fun g => ?_
      by_cases hg : g ∈ GG k r
      · rw [Measure.smul_apply, measure_mono_null (t := {n | Yj k r hj z z' γ (Matrix.of n * g) = 0}) (fun n hn => hn.2)
          (hV g hg).1, smul_zero]
      · refine measure_mono_null (t := {x | Matrix.of x ∉ Nset k r}) (fun n hn hn' => hg ?_) hN.2.2.1
        exact (WUnfold.mul_mem_GG_iff hn'.1).1 hn.1
    have hA1 : νR A = 0 := by
      refine hnull A hA (fun ρ hρ x hx => ?_) hA0
      show (ρ * Matrix.of x ∈ GG k r ∧ Yj k r hj z z' γ (ρ * Matrix.of x) = 0) ↔ (_ ∧ _)
      rw [hYi ρ hρ _ hx]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ hρ.1.1 _ hx, h.2⟩⟩
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hoff hA1)
    by_cases hx' : Matrix.of x ∈ GG k r
    · exact Or.inr ⟨hx', hx.resolve_left (not_not.2 hx')⟩
    · exact Or.inl hx'
  · set E := Eset0 k r hj z z' γ R₀ y with hE
    set Q : Set (Mt k r) := {x | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x))} with hQdef
    have hQ : MeasurableSet Q := by
      have h1 := measurable_indicator_GG (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z' hz' hT').2.2.1
      have h2 := measurableSet_GG.inter ((MeasurableSet.const (i = 0)).union (measurableSet_lt
        (measurable_const (a := 2 ^ i * H₁)) h1))
      convert h2 using 1
      ext x
      refine and_congr_right fun hx => ?_
      simp only [Set.mem_union, Set.mem_setOf_eq]
      rw [Set.indicator_of_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) (a := x) hx]
    have hEQ : E ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)} = E ∩ Q := by
      ext x
      exact and_congr_right fun hx => ⟨fun h => ⟨hx.1, h⟩, fun h => h.2⟩
    have hQi : ∀ s ∈ Sset k r z', ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q) := by
      intro s hs x hx
      show (s * Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (s * Matrix.of x))) ↔ (_ ∧ _)
      rw [Sg2_left hz' hT' hs hx]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ (WUnfold.Sset_subset _ hs) _ hx, h.2⟩⟩
    have hEi : ∀ ρ ∈ Rset k r γ, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ E ↔ x ∈ E) := by
      intro ρ hρ x hx
      show (ρ * Matrix.of x ∈ GG k r ∧ Sg2 k r z' (ρ * Matrix.of x) ≤ R₀ ∧ Sg2 k r z (γ * (ρ * Matrix.of x)) ≤ R₀ ∧
        y < Yj k r hj z z' γ (ρ * Matrix.of x) ∧ Yj k r hj z z' γ (ρ * Matrix.of x) ≤ 2 * y) ↔ (_ ∧ _)
      have e : γ * (ρ * Matrix.of x) = γ * ρ * γ⁻¹ * (γ * Matrix.of x) := by
        rw [Matrix.mul_assoc (γ * ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hγ), Matrix.mul_assoc]
      rw [hYi ρ hρ _ hx, Sg2_left hz' hT' (mem_Sset_of_mem_Nset _ hρ.1) hx, e,
        Sg2_left hz hT (mem_Sset_of_mem_Nset _ hρ.2) (hmul _ hγ _ hx)]
      exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨hmul _ hρ.1.1 _ hx, h.2⟩⟩
    set g : Mt k r → ℝ≥0∞ := fun x => (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 with hg
    have hgi : ∀ ρ ∈ Nset k r, ∀ x, Matrix.of x ∈ GG k r → g (lmulM ρ x) = g x := by
      intro ρ hρ x hx
      have h1 := hΦ 1 (isClosedSub_UWset z').2.2.1 ρ hρ _ hx
      rw [Matrix.one_mul, hπ.1.1] at h1
      have h2 : ‖ψ' ρ‖₊ = 1 := NNReal.eq (hψ ρ hρ)
      show (‖⟪w, Φ' (ρ * Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 = _
      rw [h1, inner_smul_right, nnnorm_mul, h2, one_mul]
      rfl
    have hFm : Measurable ((E ∩ Q).indicator g) := by
      have h1 : ContinuousOn (fun x : Mat k r => (‖⟪w, Φ' x⟫_ℂ‖₊ : ℝ≥0∞) ^ 2) (GG k r) :=
        (ENNReal.continuous_pow 2).comp_continuousOn
          (ENNReal.continuous_coe.comp_continuousOn (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const hΦc).nnnorm)
      have h2 := (measurable_indicator_GG h1).indicator ((hEm R₀ y).inter hQ)
      rwa [Set.indicator_indicator, Set.inter_eq_left.2 (fun x hx => hx.2.1)] at h2
    have hFi : ∀ ρ ∈ Rset k r γ, ∀ x, Matrix.of x ∈ GG k r →
        (E ∩ Q).indicator g (lmulM ρ x) = (E ∩ Q).indicator g x := by
      intro ρ hρ x hx
      have hiff : lmulM ρ x ∈ E ∩ Q ↔ x ∈ E ∩ Q :=
        and_congr (hEi ρ hρ x hx) (hQi ρ (mem_Sset_of_mem_Nset _ hρ.1) x hx)
      by_cases h : x ∈ E ∩ Q
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.2 h), hgi ρ hρ.1 x hx]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hiff.1 h)]
    have hP := GlobalTheory.T.amplitude_one_side_unfolding k r z' π' ψ' μG μW' _ νS' Φ' c hO (fun x => φ x * E.indicator 1 x) Q
      (ENNReal.ofReal κ * ENNReal.ofReal (fibVol0 k r j R₀ De y / s))
      (hφ.1.mul (measurable_one.indicator (hEm R₀ y))) hQ hQi (fun g hg => by
        rw [lintegral_smul_measure, smul_eq_mul]
        exact mul_le_mul_right ((hV g hg).2 φ hφ R₀ y hR hy) _) w hw
    have hTl := tail hz' hT' hH ht i hQ fun x hx => hx.2
    have hfib : 0 ≤ fibVol0 k r j R₀ De y := by
      have := hDe.1
      unfold fibVol0
      positivity
    have hd : (0 : ℝ) < Module.finrank ℂ Wq := Nat.cast_pos.2 Module.finrank_pos
    calc ∫⁻ x in E ∩ {x | i = 0 ∨ 2 ^ i * H₁ < Sg2 k r z' (Matrix.of x)},
          ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR
        = ∫⁻ x, (E ∩ Q).indicator g x ∂νR := by
          rw [hEQ, lintegral_indicator ((hEm R₀ y).inter hQ)]
          refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
          rfl
      _ = ∫⁻ x in Q, φ x * E.indicator 1 x * g x ∂μG := by
          rw [hcut _ hFm hFi, ← lintegral_indicator hQ]
          refine lintegral_congr fun x => ?_
          by_cases h1 : x ∈ E <;> by_cases h2 : x ∈ Q <;> simp [h1, h2]
      _ ≤ ENNReal.ofReal κ * ENNReal.ofReal (fibVol0 k r j R₀ De y / s) * (Module.finrank ℂ Wq : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal ((4 * r + 4) * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * l2SG νS' Φ') :=
          hP.trans (mul_le_mul_right hTl _)
      _ = _ := by
          rw [hl2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hd, ← ENNReal.ofReal_mul hκ.le,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp

end GlobalTheory.Amp.DegSide
