import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWIrreducibleAndSchurAverageStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OnePiece

variable {k r : ℕ}

theorem continuous_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  unfold lmulM
  exact continuous_const.matrix_mul continuous_id.matrixOf

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  unfold conjM
  exact (continuous_const.matrix_mul continuous_id.matrixOf).matrix_mul continuous_const

theorem continuous_mulPair :
    Continuous fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := by
  unfold lmulM
  exact continuous_fst.matrixOf.matrix_mul continuous_snd.matrixOf

def grp (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ GG k r}

theorem measurableSet_grp : MeasurableSet (grp k r) := by
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r)ᴴ * Hpk k r * Matrix.of x :=
    (continuous_id.matrixOf.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id.matrixOf
  exact (isClosed_eq hc continuous_const).measurableSet

private theorem continuous_matrix_of : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) :=
  continuous_id.matrixOf

theorem measurable_indicator_grp {f : Mat k r → ℝ≥0∞} (hf : ContinuousOn f (GG k r)) :
    Measurable ((grp k r).indicator fun x => f (Matrix.of x)) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise
    (hf.comp continuous_matrix_of.continuousOn fun _ hx => hx) continuousOn_const measurableSet_grp

theorem mem_GG_of_mul {s x : Mat k r} (hs : s ∈ GG k r) (h : s * x ∈ GG k r) : x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have h' : (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r := h
  show xᴴ * Hpk k r * x = Hpk k r
  calc xᴴ * Hpk k r * x = xᴴ * (sᴴ * Hpk k r * s) * x := by rw [hs']
    _ = (s * x)ᴴ * Hpk k r * (s * x) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := h'

theorem continuousOn_sq {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] {g : X → E} {s : Set X}
    (hg : ContinuousOn g s) : ContinuousOn (fun x => (‖g x‖₊ : ℝ≥0∞) ^ 2) s :=
  ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp continuous_nnnorm)).comp_continuousOn hg

private theorem mul_mem_UH_Hpk' {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem aemeasurable_comp_of_continuousOn_closed {S : Set (Mat k r)} (hS : IsClosed S) {μ : Measure (Mt k r)}
    (hμ : μ {x | Matrix.of x ∉ S} = 0) {g : Mat k r → ℝ≥0∞} (hg : ContinuousOn g S) :
    AEMeasurable (fun x => g (Matrix.of x)) μ := by
  classical
  have hm : MeasurableSet {x : Mt k r | Matrix.of x ∈ S} :=
    (hS.preimage continuous_matrix_of).measurableSet
  have h1 : Measurable ({x : Mt k r | Matrix.of x ∈ S}.piecewise (fun x => g (Matrix.of x)) 0) :=
    ContinuousOn.measurable_piecewise (hg.comp continuous_matrix_of.continuousOn fun _ hx => hx)
      continuousOn_const hm
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S := by rw [ae_iff]; exact hμ
  refine h1.aemeasurable.congr ?_
  filter_upwards [hae] with x hx
  exact Set.piecewise_eq_of_mem _ _ _ hx

private theorem ofReal_one_sq_mul_norm_sq_div {E : Type} [NormedAddCommGroup E] (v : E) (d : ℕ) (hd : 0 < d) :
    ENNReal.ofReal ((1 : ℝ) ^ 2 * ‖v‖ ^ 2 / d) = (d : ℝ≥0∞)⁻¹ * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  rw [one_pow, one_mul, div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hd'.le),
    ENNReal.ofReal_inv_of_pos hd', ENNReal.ofReal_natCast, ← coe_nnnorm v, ← NNReal.coe_pow,
    ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]

theorem one_piece : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (ψ : Mat k r → ℂ) (μG μW μN νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (c : ℝ), OneSide z π ψ μG μW μN νS Φ c → ∀ (f : Mt k r → ℝ≥0∞) (Q : Set (Mt k r)) (Vol : ℝ≥0∞), Measurable f → MeasurableSet Q → (∀ s ∈ Sset k r z, ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q)) → (∀ g ∈ GG k r, ∫⁻ n, f (rmulM g n) ∂μN ≤ Vol) → ∀ w : Wp, ‖w‖ = 1 → ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG ≤ Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS := by
  intro k r Wp _ _ _ z π ψ μG μW μN νS Φ c hOS f Q Vol hf hQ hQinv hVol w hw
  obtain ⟨hz, hT, hnt, hU, hI, hG, hW, hW1, hN, hQm, hψ, hE, hΦ, -, -⟩ := hOS
  haveI := hnt
  have hd : 0 < Module.finrank ℂ Wp := Module.finrank_pos
  have hinC : Continuous fun v : Wp => ⟪w, v⟫_ℂ := continuous_const.inner continuous_id
  set A : Mt k r → ℝ≥0∞ := (grp k r).indicator fun y => (‖⟪w, Φ (Matrix.of y)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2
    with hAdef
  set B : Mt k r → ℝ≥0∞ := (grp k r).indicator fun y => (‖Φ (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2
    with hBdef
  have hAm : Measurable A :=
    measurable_indicator_grp (f := fun g => (‖⟪w, Φ g⟫_ℂ‖₊ : ℝ≥0∞) ^ 2)
      (continuousOn_sq (hinC.comp_continuousOn hΦ))
  have hBm : Measurable B :=
    measurable_indicator_grp (f := fun g => (‖Φ g‖₊ : ℝ≥0∞) ^ 2) (continuousOn_sq hΦ)
  set F : Mt k r → ℝ≥0∞ := Q.indicator fun y => f y * A y with hFdef
  have hFm : Measurable F := (hf.mul hAm).indicator hQ
  have haeG : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := by rw [ae_iff]; exact hG.2.2.1
  have haeW : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
  have haeN : ∀ᵐ n ∂μN, Matrix.of n ∈ Nset k r := by rw [ae_iff]; exact hN.2.2.1

  have step1 : ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG = ∫⁻ x, F x ∂μG := by
    rw [← lintegral_indicator hQ]
    refine lintegral_congr_ae ?_
    filter_upwards [haeG] with x hx
    have hxg : x ∈ grp k r := hx
    by_cases hxQ : x ∈ Q
    · rw [hFdef, hAdef]
      simp only [Set.indicator_of_mem hxQ, Set.indicator_of_mem hxg]
    · rw [hFdef]
      simp only [Set.indicator_of_notMem hxQ]

  have inner_le : ∀ x : Mt k r,
      ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ≤
        Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
    intro x
    have hit : ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ≤
        ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW :=
      calc ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN)
          ≤ ∫⁻ p, F (lmulM (Matrix.of p.1 * Matrix.of p.2) x) ∂(μW.prod μN) := lintegral_map_le _ _
        _ ≤ ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW := lintegral_prod_le _
    refine hit.trans ?_
    have zero_case : (∀ h : Mt k r, Matrix.of h ∈ UWset k r z → ∀ n : Mt k r,
        Matrix.of n ∈ Nset k r → F (lmulM (Matrix.of h * Matrix.of n) x) = 0) →
        ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW ≤
          Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
      intro h0
      refine le_trans ?_ (zero_le ..)
      calc ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW
          ≤ ∫⁻ _h, (0 : ℝ≥0∞) ∂μW := by
            refine lintegral_mono_ae ?_
            filter_upwards [haeW] with h hh
            calc ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ≤ ∫⁻ _n, (0 : ℝ≥0∞) ∂μN := by
                  refine lintegral_mono_ae ?_
                  filter_upwards [haeN] with n hn
                  exact (h0 h hh n hn).le
              _ = 0 := lintegral_zero
        _ = 0 := lintegral_zero
    by_cases hxg : x ∈ grp k r
    · by_cases hxQ : x ∈ Q
      · have hB : Q.indicator B x = (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 := by
          rw [hBdef]
          simp only [Set.indicator_of_mem hxQ, Set.indicator_of_mem hxg]
        have hmain : ∀ h : Mt k r, Matrix.of h ∈ UWset k r z → ∀ n : Mt k r,
            Matrix.of n ∈ Nset k r → F (lmulM (Matrix.of h * Matrix.of n) x) =
              f (lmulM (Matrix.of h * Matrix.of n) x) *
                (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 := by
          intro h hh n hn
          have hs : Matrix.of h * Matrix.of n ∈ Sset k r z := by
            show ∃ h' ∈ UWset k r z, ∃ m ∈ Nset k r, Matrix.of h * Matrix.of n = h' * m
            exact ⟨_, hh, _, hn, rfl⟩
          have hSQ : lmulM (Matrix.of h * Matrix.of n) x ∈ Q := (hQinv _ hs x hxg).2 hxQ
          have hSG : lmulM (Matrix.of h * Matrix.of n) x ∈ grp k r :=
            mul_mem_UH_Hpk' (mul_mem_UH_Hpk' hh.1 hn.1) hxg
          have hΦS : Φ (Matrix.of (lmulM (Matrix.of h * Matrix.of n) x)) =
              ψ (Matrix.of n) • π (Matrix.of h) (Φ (Matrix.of x)) := hE _ hh _ hn _ hxg
          have hψ1 : ‖ψ (Matrix.of n)‖₊ = 1 := by ext; simpa using hψ _ hn
          rw [hFdef, hAdef]
          simp only [Set.indicator_of_mem hSQ, Set.indicator_of_mem hSG, hΦS, inner_smul_right,
            nnnorm_mul, hψ1, one_mul]
        have hfib : ∀ h : Mt k r, Matrix.of h ∈ UWset k r z →
            ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ≤ Vol := by
          intro h hh
          have hdet : IsUnit (Matrix.of h : Mat k r).det := isUnit_det_of_mem_GG hh.1
          have key : ∀ n : Mt k r, lmulM (Matrix.of h * Matrix.of n) x =
              rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n) := by
            intro n
            show (Matrix.of h * Matrix.of n * Matrix.of x : Mat k r) =
              Matrix.of h * Matrix.of n * (Matrix.of h)⁻¹ * (Matrix.of h * Matrix.of x)
            rw [Matrix.mul_assoc (Matrix.of h * Matrix.of n) (Matrix.of h)⁻¹,
              ← Matrix.mul_assoc (Matrix.of h)⁻¹, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
          have hrc : Continuous (rmulM (Matrix.of h * Matrix.of x) : Mt k r → Mt k r) := by
            unfold rmulM
            exact continuous_matrix_of.matrix_mul continuous_const
          have hinv : μN.map (conjM (Matrix.of h)) = μN :=
            ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μN).2.1 hN).2 _ hh
          calc ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN
              = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n)) ∂μN :=
                lintegral_congr fun n => congrArg f (key n)
            _ = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) n) ∂(μN.map (conjM (Matrix.of h))) :=
                (lintegral_map (hf.comp hrc.measurable) (continuous_conj _).measurable).symm
            _ = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) n) ∂μN := by rw [hinv]
            _ ≤ Vol := hVol _ (mul_mem_UH_Hpk' hh.1 hxg)
        have hAEM : AEMeasurable (fun h : Mt k r =>
            (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2) μW :=
          aemeasurable_comp_of_continuousOn_closed (isClosedSub_UWset z).2.1 hW.2.2.1
            (g := fun g => (‖⟪w, π g (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2)
            (continuousOn_sq (hinC.comp_continuousOn (hU.2.2 (Φ (Matrix.of x)))))
        calc ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW
            ≤ ∫⁻ h, Vol * (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW := by
              refine lintegral_mono_ae ?_
              filter_upwards [haeW] with h hh
              calc ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN
                  = ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) *
                      (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μN := by
                    refine lintegral_congr_ae ?_
                    filter_upwards [haeN] with n hn
                    exact hmain h hh n hn
                _ = (∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN) *
                      (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
                    lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)
                _ ≤ Vol * (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
                    mul_le_mul_of_nonneg_right (hfib h hh) (zero_le ..)
          _ = Vol * ∫⁻ h, (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW :=
              lintegral_const_mul'' _ hAEM
          _ = Vol * ENNReal.ofReal (‖w‖ ^ 2 * ‖Φ (Matrix.of x)‖ ^ 2 / Module.finrank ℂ Wp) := by
              rw [(GlobalTheory.T.hcTypeW_irreducible_and_schur_average k r z π hz hT).2 μW hU hI hW hW1 w (Φ (Matrix.of x))]
          _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
              rw [hB, hw, ofReal_one_sq_mul_norm_sq_div _ _ hd, mul_assoc]
      · refine zero_case fun h hh n hn => ?_
        have hs : Matrix.of h * Matrix.of n ∈ Sset k r z := by
          show ∃ h' ∈ UWset k r z, ∃ m ∈ Nset k r, Matrix.of h * Matrix.of n = h' * m
          exact ⟨_, hh, _, hn, rfl⟩
        have hSQ : lmulM (Matrix.of h * Matrix.of n) x ∉ Q := fun h' => hxQ ((hQinv _ hs x hxg).1 h')
        rw [hFdef]
        simp only [Set.indicator_of_notMem hSQ]
    · refine zero_case fun h hh n hn => ?_
      have hS : lmulM (Matrix.of h * Matrix.of n) x ∉ grp k r := fun hS =>
        hxg (mem_GG_of_mul (s := Matrix.of h * Matrix.of n) (x := Matrix.of x)
          (mul_mem_UH_Hpk' hh.1 hn.1) hS)
      rw [hFdef, hAdef]
      by_cases hSQ : lmulM (Matrix.of h * Matrix.of n) x ∈ Q
      · simp only [Set.indicator_of_mem hSQ, Set.indicator_of_notMem hS, mul_zero]
      · simp only [Set.indicator_of_notMem hSQ]
  calc ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG = ∫⁻ x, F x ∂μG := step1
    _ = ∫⁻ x, ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ∂νS := hQm F hFm
    _ ≤ ∫⁻ x, Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x ∂νS := lintegral_mono inner_le
    _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x, Q.indicator B x ∂νS :=
        lintegral_const_mul _ (hBm.indicator hQ)
    _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, B x ∂νS := by rw [lintegral_indicator hQ]
    _ ≤ Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS :=
        mul_le_mul_of_nonneg_left (lintegral_mono fun x => Set.indicator_le_self _ _ x) (zero_le ..)

end GlobalTheory.Amp.OnePiece
