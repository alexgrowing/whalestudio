import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TailMassLeOfMajorantLengthMomentBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormRootMeasureHaarUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreVolumeTwoFlagsGeneralPositionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberAndFibreSetsMeasurableStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsSide

variable {k r : ℕ}

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem continuous_mulPair :
    Continuous fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 :=
  (continuous_fst (X := Mat k r) (Y := Mat k r)).matrix_mul continuous_snd

theorem measurableSet_grp : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  have hc : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := isClosedSub_GG.2.1
  exact hc.measurableSet

theorem measurable_indicator_grp {B : Type} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [Zero B]
    {f : Mat k r → B} (hf : ContinuousOn f (GG k r)) :
    Measurable (({x : Mt k r | Matrix.of x ∈ GG k r}).indicator fun x => f (Matrix.of x)) := by
  classical
  have h1 : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) {x : Mt k r | Matrix.of x ∈ GG k r} := hf
  have := ContinuousOn.measurable_piecewise (g := fun _ => (0 : B)) h1 continuousOn_const measurableSet_grp
  convert this using 1
  exact (Set.piecewise_eq_indicator).symm

theorem mul_mem {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  isClosedSub_GG.2.2.2.1 _ ha _ hb

theorem mem_GG_of_mul {s x : Mat k r} (hs : s ∈ GG k r) (h : s * x ∈ GG k r) : x ∈ GG k r := by
  have := mul_mem (isClosedSub_GG.2.2.2.2 _ hs) h
  rwa [Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hs)] at this

theorem continuousOn_sq {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] {g : X → E} {s : Set X}
    (hg : ContinuousOn g s) : ContinuousOn (fun x => (‖g x‖₊ : ℝ≥0∞) ^ 2) s :=
  (ENNReal.continuous_pow 2).comp_continuousOn (ENNReal.continuous_coe.comp_continuousOn hg.nnnorm)

theorem lintegral_muProd {μW μN : Measure (Mt k r)} [SFinite μN] {F : Mt k r → ℝ≥0∞} (hF : Measurable F)
    (x : Mt k r) : ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) =
      ∫⁻ h, ∫⁻ n, F (rmulM (Matrix.of x) (lmulM (Matrix.of h) n)) ∂μN ∂μW := by
  have hm : Measurable fun s : Mt k r => F (rmulM (Matrix.of x) s) := hF.comp (continuous_rmulM _).measurable
  refine (lintegral_map hm continuous_mulPair.measurable).trans ?_
  exact lintegral_prod _ (hm.comp continuous_mulPair.measurable).aemeasurable

theorem quot_conc {z : Fin (2 * r + k + 1) → ℂ} {μG μW μN νS : Measure (Mt k r)} (hG : IsHaarOn (GG k r) μG)
    (hW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1) (hN : IsHaarOn (Nset k r) μN)
    (hq : IsQuotMeas μG (muProd μW μN) νS) : νS {x | Matrix.of x ∉ GG k r} = 0 := by
  haveI := hN.1
  have aeW : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := ae_iff.2 hW.2.2.1
  have aeN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := ae_iff.2 hN.2.2.1
  set A : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hA
  have hAm : MeasurableSet A := measurableSet_grp.compl
  have hf : Measurable (A.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hAm
  have h0 := hq _ hf
  rw [lintegral_indicator_one hAm, hG.2.2.1] at h0
  have h1 : ∫⁻ x, A.indicator (fun _ => μN Set.univ) x ∂νS ≤ 0 := by
    rw [h0]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, lintegral_muProd hf]
      refine le_of_eq (Eq.symm ?_)
      calc _ = ∫⁻ _, μN Set.univ ∂μW := by
            refine lintegral_congr_ae (aeW.mono fun h hh => ?_)
            rw [← lintegral_one]
            refine lintegral_congr_ae (aeN.mono fun n hn => ?_)
            have : rmulM (Matrix.of x) (lmulM (Matrix.of h) n) ∈ A := fun h' =>
              hx (mem_GG_of_mul (mul_mem hh.1 hn.1) h')
            exact Set.indicator_of_mem this _
        _ = _ := by rw [lintegral_const, hW1, mul_one]
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  rw [lintegral_indicator_const hAm, nonpos_iff_eq_zero, mul_eq_zero] at h1
  exact h1.resolve_left fun h => hN.2.1 (Measure.measure_univ_eq_zero.1 h)

theorem null_of_fibres {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μG μW μN νS : Measure (Mt k r)} (hG : IsHaarOn (GG k r) μG)
    (hW : IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1) (hN : IsHaarOn (Nset k r) μN)
    (hq : IsQuotMeas μG (muProd μW μN) νS) {A : Set (Mt k r)} (hAm : MeasurableSet A)
    (hA : ∀ g ∈ GG k r, μN {n | rmulM g n ∈ A} = 0) : μG A = 0 := by
  haveI := hN.1
  have aeW : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := ae_iff.2 hW.2.2.1
  have aeS : ∀ᵐ x ∂νS, Matrix.of x ∈ GG k r := ae_iff.2 (quot_conc hG hW hW1 hN hq)
  have hf : Measurable (A.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hAm
  rw [← lintegral_indicator_one hAm, hq _ hf, ← lintegral_zero (μ := νS)]
  refine lintegral_congr_ae (aeS.mono fun x hx => ?_)
  refine (lintegral_muProd hf x).trans ?_
  rw [← lintegral_zero (μ := μW)]
  refine lintegral_congr_ae (aeW.mono fun h hh => ?_)
  have hg : Matrix.of h * Matrix.of x ∈ GG k r := mul_mem hh.1 hx
  have hm2 : Measurable fun n : Mt k r => A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of h * Matrix.of x) n) :=
    hf.comp (continuous_rmulM _).measurable
  have hc := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μN).2.1 hN).2 _ hh
  calc ∫⁻ n, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of x) (lmulM (Matrix.of h) n)) ∂μN
      = ∫⁻ n, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n)) ∂μN := by
        refine lintegral_congr fun n => ?_
        congr 1
        show Matrix.of h * Matrix.of n * Matrix.of x =
          Matrix.of h * Matrix.of n * (Matrix.of h)⁻¹ * (Matrix.of h * Matrix.of x)
        rw [Matrix.mul_assoc _ (Matrix.of h)⁻¹,
          Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hh.1)]
    _ = ∫⁻ n, A.indicator (1 : Mt k r → ℝ≥0∞) (rmulM (Matrix.of h * Matrix.of x) n) ∂μN := by
        refine (lintegral_map hm2 (continuous_conj (Matrix.of h)).measurable).symm.trans ?_
        rw [hc]
    _ = 0 := by
        rw [← hA _ hg]
        exact lintegral_indicator_one (s := {n | rmulM (Matrix.of h * Matrix.of x) n ∈ A})
          ((continuous_rmulM _).measurable hAm)

theorem N_sub_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, (isClosedSub_UWset z).2.2.1, n, hn, (Matrix.one_mul n).symm⟩

theorem Sg_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {s x : Mat k r} (hs : s ∈ Sset k r z)
    (hx : x ∈ GG k r) : Sg k r z (s * x) = Sg k r z x := by
  have := ((GlobalTheory.Amp.LInv.lengths_basic k r z hz).1 x hx s hs 1 ⟨isClosedSub_GG.2.2.1, one_mem _⟩).2
  rwa [Matrix.mul_one] at this

theorem Eset_inv {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {γ ρ : Mat k r}
    (hγ : γ ∈ GG k r) (hρ : ρ ∈ Rset k r γ) {x : Mt k r} (hx : Matrix.of x ∈ GG k r) (R₀ y : ℝ) :
    lmulM ρ x ∈ Eset k r z z' γ R₀ y ↔ x ∈ Eset k r z z' γ R₀ y := by
  have h1 : Sg k r z' (ρ * Matrix.of x) = Sg k r z' (Matrix.of x) := Sg_inv hz' (N_sub_S z' hρ.1) hx
  have h2 : Sg k r z (γ * (ρ * Matrix.of x)) = Sg k r z (γ * Matrix.of x) := by
    rw [← Sg_inv hz (N_sub_S z hρ.2) (mul_mem hγ hx), Matrix.mul_assoc _ γ⁻¹,
      Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hγ), Matrix.mul_assoc]
  have h3 := (GlobalTheory.Amp.YInv.yv_invariant k r z z' γ hz hz' hγ _ hx).2.2 ρ hρ
  have h4 : ρ * Matrix.of x ∈ GG k r := mul_mem hρ.1.1 hx
  show (ρ * Matrix.of x ∈ GG k r ∧ Sg k r z' (ρ * Matrix.of x) ≤ R₀ ∧ Sg k r z (γ * (ρ * Matrix.of x)) ≤ R₀ ∧
    y < Yv k r z z' γ (ρ * Matrix.of x) ∧ Yv k r z z' γ (ρ * Matrix.of x) ≤ 2 * y) ↔
    (Matrix.of x ∈ GG k r ∧ Sg k r z' (Matrix.of x) ≤ R₀ ∧ Sg k r z (γ * (Matrix.of x)) ≤ R₀ ∧
    y < Yv k r z z' γ (Matrix.of x) ∧ Yv k r z z' γ (Matrix.of x) ≤ 2 * y)
  rw [h1, h2, h3]
  simp only [h4, hx]

theorem abs_side : ∀ (k r : ℕ) {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ' : Mat k r → ℂ) (μG μW' νS' μR νR : Measure (Mt k r)) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → MomBd z' νS' Φ' q H₁ → TwoFl k r z z' γ → DeOK k r z z' γ De → NormR k r γ s μR → IsQuotMeas μG μR νR → νR {x | Matrix.of x ∉ GG k r ∨ Yv k r z z' γ (Matrix.of x) = 0} = 0 ∧ ∀ w : Wq, ‖w‖ = 1 → ∀ (i : ℕ) (R₀ y : ℝ), 1 ≤ R₀ → 0 < y → ∫⁻ x in Eset k r z z' γ R₀ y ∩ {x | i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z' (Matrix.of x)}, ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR ≤ ENNReal.ofReal (κ / s * fibVol k r R₀ De y * ((r + 1) * 4 ^ q * ((2 ^ i : ℝ) ^ (2 * q))⁻¹) * c) := by
  intro k r Wq _ _ _ z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De q hr hk hκ hs hH hO hM hF hD hR hQ
  have hO' := hO
  obtain ⟨hz', hT', hnt, hU, -, hG, hW, hW1, hN, hq, hψ, hE, hΦ, hc, hl2⟩ := hO'
  have hz := hF.1
  have hγ : γ ∈ GG k r := hF.2.2.2.2.1
  obtain ⟨hRc, hRh, hRu, -⟩ := GlobalTheory.T.normalFormRootMeasure_haar_unimodular k r γ s μR hs hR
  obtain ⟨-, hnull, φ, hφ, hcut⟩ := GlobalTheory.Amp.CutQuot.cut_quotient k r _ μG μR νR hRc hG hRh hRu hQ
  have hP := GlobalTheory.T.fibreVolume_twoFlags_generalPosition k r z z' γ De s μR hr hk hF hD hs hR
  obtain ⟨hYm, hEm⟩ := GlobalTheory.T.twoFlagsGramNumber_and_fibre_sets_measurable k r z z' γ hγ
  refine ⟨?_, ?_⟩
  · have hAm : MeasurableSet {x : Mt k r | Matrix.of x ∉ GG k r ∨ Yv k r z z' γ (Matrix.of x) = 0} := by
      convert hYm (measurableSet_singleton 0) using 1
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, Set.indicator_apply_eq_zero]
      tauto
    refine hnull _ hAm (fun ρ hρ x hx => ?_) (null_of_fibres hz' hT' hG hW hW1 hN hq hAm fun g hg => ?_)
    · have h3 := (GlobalTheory.Amp.YInv.yv_invariant k r z z' γ hz hz' hγ _ hx).2.2 ρ hρ
      have h4 : ρ * Matrix.of x ∈ GG k r := mul_mem hρ.1.1 hx
      show (ρ * Matrix.of x ∉ GG k r ∨ Yv k r z z' γ (ρ * Matrix.of x) = 0) ↔
        (Matrix.of x ∉ GG k r ∨ Yv k r z z' γ (Matrix.of x) = 0)
      rw [h3]
      simp only [h4, hx]
    · have h2 : (ENNReal.ofReal κ • lebN k r) {n | Yv k r z z' γ (Matrix.of n * g) = 0} = 0 := by
        rw [Measure.smul_apply, (hP g hg).1, smul_zero]
      refine measure_mono_null (fun n hn => ?_) (measure_union_null hN.2.2.1 h2)
      rcases hn with hn | hn
      · exact Or.inl fun h => hn (mul_mem h.1 hg)
      · exact Or.inr hn
  intro w hw i R₀ y hR₀ hy
  set E := Eset k r z z' γ R₀ y with hEdef
  set Q : Set (Mt k r) :=
    {x | Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z' (Matrix.of x))} with hQdef
  have hQm : MeasurableSet Q := by
    have h1 := measurable_indicator_grp (GlobalTheory.Amp.LenCont.lA_Sg_continuousOn k r z').2
    have h2 := measurableSet_grp.inter ((MeasurableSet.const (i = 0)).union
      (h1 (measurableSet_Ioi (a := 2 ^ i * H₁ / 2))))
    convert h2 using 1
    ext x
    by_cases hx : Matrix.of x ∈ GG k r
    · have : x ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := hx
      simp only [hQdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union, Set.mem_preimage, Set.mem_Ioi,
        Set.indicator_of_mem this]
    · simp only [hQdef, Set.mem_setOf_eq, Set.mem_inter_iff, hx, false_and]
  have hQS : ∀ s ∈ Sset k r z', ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q) := by
    intro s hs x hx
    have h4 : s * Matrix.of x ∈ GG k r := mul_mem ((isClosedSub_Sset hz' hT').1 hs) hx
    show (s * Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z' (s * Matrix.of x))) ↔
      (Matrix.of x ∈ GG k r ∧ (i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z' (Matrix.of x)))
    rw [Sg_inv hz' hs hx]
    simp only [h4, hx]
  have hEQ : E ∩ {x | i = 0 ∨ 2 ^ i * H₁ / 2 < Sg k r z' (Matrix.of x)} = E ∩ Q :=
    Set.ext fun x => ⟨fun h => ⟨h.1, h.1.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have hEQm : MeasurableSet (E ∩ Q) := (hEm R₀ y).inter hQm
  set a : Mt k r → ℝ≥0∞ := ({x : Mt k r | Matrix.of x ∈ GG k r}).indicator
    fun x => (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 with ha
  have ham : Measurable a :=
    measurable_indicator_grp (f := fun x => (‖⟪w, Φ' x⟫_ℂ‖₊ : ℝ≥0∞) ^ 2)
      (continuousOn_sq (ContinuousOn.inner continuousOn_const hΦ))
  have haG : ∀ x : Mt k r, Matrix.of x ∈ GG k r → a x = (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
    fun x hx => Set.indicator_of_mem (s := {x : Mt k r | Matrix.of x ∈ GG k r}) hx _
  have hinv : ∀ ρ ∈ Rset k r γ, ∀ x, Matrix.of x ∈ GG k r →
      (E ∩ Q).indicator a (lmulM ρ x) = (E ∩ Q).indicator a x := by
    intro ρ hρ x hx
    have h1 : lmulM ρ x ∈ E ∩ Q ↔ x ∈ E ∩ Q :=
      and_congr (Eset_inv hz hz' hγ hρ hx R₀ y) (hQS ρ (N_sub_S z' hρ.1) x hx)
    by_cases h : x ∈ E ∩ Q
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (h1.2 h), haG x hx, haG (lmulM ρ x) (mul_mem hρ.1.1 hx)]
      have h2 := hE 1 (isClosedSub_UWset z').2.2.1 ρ hρ.1 _ hx
      rw [Matrix.one_mul, hU.1.1] at h2
      have hψ' : ‖ψ' ρ‖₊ = 1 := NNReal.eq (hψ ρ hρ.1)
      show (‖⟪w, Φ' (ρ * Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 = _
      rw [h2, inner_smul_right, nnnorm_mul, hψ', one_mul]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h (h1.1 h')]
  have hfm : Measurable fun x => φ x * E.indicator 1 x := hφ.1.mul (measurable_one.indicator (hEm R₀ y))
  have hpiece := GlobalTheory.T.amplitude_one_side_unfolding k r z' π' ψ' μG μW' _ νS' Φ' c hO (fun x => φ x * E.indicator 1 x) Q
    (ENNReal.ofReal κ * ENNReal.ofReal (fibVol k r R₀ De y / s)) hfm hQm hQS (fun g hg => by
      rw [lintegral_smul_measure, smul_eq_mul]
      exact mul_le_mul_right ((hP g hg).2 φ hφ R₀ y hR₀ hy) _) w hw
  have hcheb := GlobalTheory.T.tail_mass_le_of_majorantLengthMomentBound k r z' νS' Φ' q H₁ hH (quot_conc hG hW hW1 hN hq) hΦ hM i
  have hd : (0 : ℝ) < Module.finrank ℂ Wq := by exact_mod_cast Module.finrank_pos
  have hV : 0 ≤ fibVol k r R₀ De y := by
    have := hD.1
    unfold fibVol
    positivity
  rw [hEQ]
  calc ∫⁻ x in E ∩ Q, ENNReal.ofReal (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖ ^ 2) ∂νR
      = ∫⁻ x, (E ∩ Q).indicator a x ∂νR := by
        rw [lintegral_indicator hEQm]
        refine setLIntegral_congr_fun hEQm fun x hx => ?_
        rw [haG x hx.2.1, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
        rfl
    _ = ∫⁻ x, φ x * (E ∩ Q).indicator a x ∂μG := hcut _ (ham.indicator hEQm) hinv
    _ = ∫⁻ x in Q, φ x * E.indicator 1 x * (‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG := by
        rw [← lintegral_indicator hQm]
        refine lintegral_congr fun x => ?_
        by_cases h1 : x ∈ Q
        · rw [Set.indicator_of_mem h1]
          by_cases h2 : x ∈ E
          · rw [Set.indicator_of_mem (Set.mem_inter h2 h1), Set.indicator_of_mem h2, haG x h1.1, Pi.one_apply, mul_one]
          · rw [Set.indicator_of_notMem (fun h => h2 h.1), Set.indicator_of_notMem h2, mul_zero, zero_mul]
        · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun h => h1 h.2), mul_zero]
    _ ≤ _ := hpiece
    _ ≤ _ := mul_le_mul_right hcheb _
    _ = _ := by
        rw [hl2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hd, ← ENNReal.ofReal_mul hκ.le,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end GlobalTheory.Amp.AbsSide
