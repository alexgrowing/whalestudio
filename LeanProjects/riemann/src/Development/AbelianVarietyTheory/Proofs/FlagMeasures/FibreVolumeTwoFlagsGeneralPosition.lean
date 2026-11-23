import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreGramNumberNullAndCutoffIntegralBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOnStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreVolumeGen

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem GG_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ (Hpk k r) hpk_unit).2.1 a ha b hb

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det :=
  ((uHGroup _ (Hpk k r) hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r :=
  ((uHGroup _ (Hpk k r) hpk_unit).2.2 a ha).2

theorem N_sub_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  GlobalTheory.Amp.YInv.N_sub_S z hn

theorem continuous_two (a b : Mat k r) : Continuous (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem measurable_two (a b : Mat k r) :
    Measurable (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) := by
  have h : Continuous (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) := continuous_two a b
  exact h.measurable

def twoEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := Matrix.of.symm (a * Matrix.of x * b)
  invFun x := Matrix.of.symm (a⁻¹ * Matrix.of x * b⁻¹)
  left_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hb]
  right_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ hb]
  measurable_toFun := measurable_two a b
  measurable_invFun := measurable_two _ _

theorem map_twoEquiv {μ : Measure (Mt k r)} {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hl : μ.map (lmulM a) = μ) (hr : μ.map (rmulM b) = μ) : μ.map (twoEquiv a b ha hb) = μ := by
  have hla : Measurable (lmulM a : Mt k r → Mt k r) := by
    have h : (lmulM a : Mt k r → Mt k r) = fun x => (Matrix.of.symm (a * Matrix.of x * 1) : Mt k r) := by
      funext x; apply Matrix.of.injective; (rw [Equiv.apply_symm_apply, Matrix.mul_one]) <;> rfl
    rw [h]; exact measurable_two a 1
  have hrb : Measurable (rmulM b : Mt k r → Mt k r) := (GlobalTheory.SgInf.continuous_rmulM b).measurable
  have h1 : (twoEquiv a b ha hb : Mt k r → Mt k r) = rmulM b ∘ lmulM a := rfl
  rw [h1, ← Measure.map_map hrb hla, hl, hr]

theorem fibre_volume : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' γ → DeOK k r z z' γ De → 0 < s → NormR k r γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yv k r z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset k r z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y / s) := by
  intro k r z z' γ De s μR hr hk hTF hDe hs hNR g₁ hg₁
  obtain ⟨n₁, hn₁, n₂, hn₂, g₀, β, hNorm, rfl, rfl⟩ := hNR
  obtain ⟨hz, hz', hT, hT', -, hGf, hDr⟩ := hTF
  have hg₀G : g₀ ∈ GG k r := hNorm.1
  have hn₁S : n₁ ∈ Sset k r z := GlobalTheory.Amp.YInv.N_sub_S z hn₁
  have hn₂S : n₂ ∈ Sset k r z' := GlobalTheory.Amp.YInv.N_sub_S z' hn₂
  have hn₂G : n₂ ∈ GG k r := hn₂.1
  have hu2 : IsUnit n₂.det := GG_unit hn₂G
  have hn₂i : n₂⁻¹ ∈ Nset k r := (nSubgroup k r).2.2 n₂ hn₂
  have hn₂iS : n₂⁻¹ ∈ Sset k r z' := GlobalTheory.Amp.YInv.N_sub_S z' hn₂i
  have c1 : ∀ B : Mat k r, n₂ * (n₂⁻¹ * B) = B := fun B => Matrix.mul_nonsing_inv_cancel_left n₂ B hu2
  have c2 : ∀ B : Mat k r, n₂⁻¹ * (n₂ * B) = B := fun B => Matrix.nonsing_inv_mul_cancel_left n₂ B hu2

  have hDmin : ∀ l, Dmin k r z z' (n₁ * g₀ * n₂) l = Dmin k r z z' g₀ l :=
    fun l => dInv k r z z' hz hz' n₁ hn₁S n₂ hn₂S g₀ l
  have hGf0 : Gf k r z z' (n₁ * g₀ * n₂) = Gf k r z z' g₀ := gInv k r z z' hz hz' n₁ hn₁S n₂ hn₂S g₀
  have hDr0 : Dr k r z z' (n₁ * g₀ * n₂) = Dr k r z z' g₀ := by unfold Dr; rw [hDmin]
  have hTF0 : TwoFl k r z z' g₀ := ⟨hz, hz', hT, hT', hg₀G, by rw [← hGf0]; exact hGf, by rw [← hDr0]; exact hDr⟩
  have hDe0 : DeOK k r z z' g₀ De := by
    refine ⟨hDe.1, fun l hl hne => ?_⟩
    rw [← hDmin] at hne ⊢
    exact hDe.2 l hl hne

  obtain ⟨n', hn', a, ha, m, hm, κ, hκ, hdec⟩ := GlobalTheory.Amp.Iwa.iwasawa k r (n₂ * g₁) (GG_mul hn₂G hg₁)
  have hB := GlobalTheory.T.fibre_gramNumber_null_and_cutoff_integral_bound k r z z' g₀ β De hr hk hTF0 hNorm hDe0 m hm a ha
  set A := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hA
  have hn'G : n' ∈ GG k r := hn'.1
  have hdec' : n₂ * g₁ = n' * A * κ := by rw [hdec, hA]; simp only [mul_assoc]
  have c3 : ∀ B : Mat k r, n'⁻¹ * (n' * B) = B := fun B => Matrix.nonsing_inv_mul_cancel_left n' B (GG_unit hn'G)
  have hAK : A * κ ∈ GG k r := by
    have : A * κ = n'⁻¹ * (n₂ * g₁) := by rw [hdec']; simp only [mul_assoc, c3]
    rw [this]; exact GG_mul (GG_inv hn'G) (GG_mul hn₂G hg₁)
  have hg : n₂⁻¹ * (n' * (A * κ)) = g₁ := by rw [← mul_assoc n' A, ← hdec', c2]

  have hl2 : (lebN k r).map (lmulM n₂) = lebN k r := (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r).2.2.2 n₂ hn₂
  have hr2 : (lebN k r).map (rmulM (n₂⁻¹ * n')) = lebN k r :=
    ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT (lebN k r)).2.1 (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r)).1.1 _ ((nSubgroup k r).2.1 _ hn₂i _ hn')
  have hu' : IsUnit (n₂⁻¹ * n').det := GG_unit (GG_mul (GG_inv hn₂G) hn'G)
  obtain ⟨e, he_map, he⟩ : ∃ e : Mt k r ≃ᵐ Mt k r, (lebN k r).map e = lebN k r ∧
      ∀ n, Matrix.of (e n) = n₂ * Matrix.of n * (n₂⁻¹ * n') :=
    ⟨twoEquiv n₂ (n₂⁻¹ * n') hu2 hu', map_twoEquiv hu2 hu' hl2 hr2, fun _ => rfl⟩
  have key : ∀ n : Mt k r, Matrix.of n * g₁ = n₂⁻¹ * (Matrix.of (e n) * A) * κ := by
    intro n; rw [he n]; simp only [mul_assoc, c2, hg]

  have hYv : ∀ W : Mat k r, Yv k r z z' (n₁ * g₀ * n₂) (n₂⁻¹ * W * κ) = Yv k r z z' g₀ W := by
    intro W
    rw [GlobalTheory.Amp.YInv.Yv_N hz hz' g₀ hn₁ hn₂]
    have : n₂ * (n₂⁻¹ * W * κ) = W * κ := by simp only [mul_assoc, c1]
    rw [this, GlobalTheory.Amp.YInv.Yv_K z z' g₀ W hκ.1 hκ.2]
  have hGGW : ∀ W : Mat k r, n₂⁻¹ * W * κ ∈ GG k r ↔ W ∈ GG k r := by
    intro W
    constructor
    · intro h
      have : W = n₂ * (n₂⁻¹ * W * κ) * κ⁻¹ := by
        simp only [mul_assoc, c1, Matrix.mul_nonsing_inv _ (GG_unit hκ.1), Matrix.mul_one]
      rw [this]; exact GG_mul (GG_mul hn₂G h) (GG_inv hκ.1)
    · intro h; exact GG_mul (GG_mul (GG_inv hn₂G) h) hκ.1
  have hSg' : ∀ W ∈ GG k r, Sg k r z' (n₂⁻¹ * W * κ) = Sg k r z' W :=
    fun W hW => ((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 W hW n₂⁻¹ hn₂iS κ hκ).2
  have hSg : ∀ W ∈ GG k r, Sg k r z (n₁ * g₀ * n₂ * (n₂⁻¹ * W * κ)) = Sg k r z (g₀ * W) := by
    intro W hW
    have : n₁ * g₀ * n₂ * (n₂⁻¹ * W * κ) = n₁ * (g₀ * W) * κ := by simp only [mul_assoc, c1]
    rw [this]; exact ((GlobalTheory.Amp.LInv.lengths_basic k r z hz).1 (g₀ * W) (GG_mul hg₀G hW) n₁ hn₁S κ hκ).2
  refine ⟨?_, ?_⟩
  · have hset : {n : Mt k r | Yv k r z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = 0} =
        e ⁻¹' {ν | Yv k r z z' g₀ (Matrix.of ν * A) = 0} := by
      ext n; simp only [Set.mem_setOf_eq, Set.mem_preimage, key n, hYv]
    rw [hset, ← MeasurableEquiv.map_apply, he_map]
    exact hB.1
  · intro φ hφ R₀ y hR₀ hy
    have hl : ∀ (b : Mat k r) (x : Mt k r), Matrix.of (lmulM b x) = b * Matrix.of x := fun _ _ => rfl
    have hc : ∀ (b : Mat k r) (x : Mt k r), Matrix.of (conjM b x) = b * Matrix.of x * b⁻¹ := fun _ _ => rfl
    have hmeas : ∀ (f : Mt k r → Mt k r) (b c : Mat k r), (∀ x, Matrix.of (f x) = b * Matrix.of x * c) →
        Measurable f := by
      intro f b c h
      have : f = fun x => (Matrix.of.symm (b * Matrix.of x * c) : Mt k r) :=
        funext fun x => Matrix.of.injective (by rw [h] <;> rfl)
      rw [this]; exact measurable_two b c
    obtain ⟨P, hPm, hP⟩ : ∃ P : Mt k r → Mt k r, Measurable P ∧
        ∀ ν, Matrix.of (P ν) = n₂⁻¹ * Matrix.of ν * (A * κ) :=
      ⟨fun ν => Matrix.of.symm (n₂⁻¹ * Matrix.of ν * (A * κ)), measurable_two _ _, fun _ => rfl⟩

    have hsub : SubCut (Nset k r) (lebR k r β) (fun ν => ENNReal.ofReal s * φ (P ν)) := by
      refine ⟨(hφ.1.comp hPm).const_mul _, fun x hx => ?_⟩
      have hx0 : Matrix.of (P x) ∈ GG k r := by
        rw [hP, mul_assoc]; exact GG_mul (GG_inv hn₂G) (GG_mul hx.1 hAK)
      have h1 := hφ.2 (P x) hx0
      have hm1 : Measurable fun ρ : Mt k r => φ (lmulM (Matrix.of ρ) (P x)) :=
        hφ.1.comp (hmeas _ 1 (Matrix.of (P x)) fun ρ => by simp only [hl, Matrix.one_mul])
      have hm2 : Measurable (conjM n₂⁻¹ : Mt k r → Mt k r) := hmeas _ n₂⁻¹ n₂⁻¹⁻¹ fun x => hc _ _
      rw [lintegral_map hm1 hm2, lintegral_smul_measure] at h1
      have hPl : ∀ ρ : Mt k r, P (lmulM (Matrix.of ρ) x) = lmulM (Matrix.of (conjM n₂⁻¹ ρ)) (P x) := by
        intro ρ
        apply Matrix.of.injective
        simp only [hl, hc, hP, Matrix.nonsing_inv_nonsing_inv _ hu2, mul_assoc, c1]
      calc ∫⁻ ρ, ENNReal.ofReal s * φ (P (lmulM (Matrix.of ρ) x)) ∂lebR k r β
          = ENNReal.ofReal s * ∫⁻ ρ, φ (P (lmulM (Matrix.of ρ) x)) ∂lebR k r β :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal s * ∫⁻ ρ, φ (lmulM (Matrix.of (conjM n₂⁻¹ ρ)) (P x)) ∂lebR k r β := by
            congr 1; exact lintegral_congr fun ρ => by rw [hPl ρ]
        _ ≤ 1 := by first | exact h1 | (rw [smul_eq_mul] at h1; exact h1)
    have hmain := hB.2 (fun ν => ENNReal.ofReal s * φ (P ν)) hsub R₀ y hR₀ hy
    have hmem : ∀ n : Mt k r, rmulM g₁ n ∈ Eset k r z z' (n₁ * g₀ * n₂) R₀ y ↔
        rmulM A (e n) ∈ Eset k r z z' g₀ R₀ y := by
      intro n
      simp only [Eset, Set.mem_setOf_eq, GlobalTheory.SgInf.of_rmulM]
      rw [key n]
      generalize Matrix.of (e n) * A = W
      rw [hGGW W, hYv W]
      constructor
      · rintro ⟨hW, h1, h2, h3, h4⟩
        rw [hSg' W hW] at h1; rw [hSg W hW] at h2; exact ⟨hW, h1, h2, h3, h4⟩
      · rintro ⟨hW, h1, h2, h3, h4⟩
        exact ⟨hW, by rw [hSg' W hW]; exact h1, by rw [hSg W hW]; exact h2, h3, h4⟩
    have hpt : ∀ n : Mt k r, rmulM g₁ n = P (e n) := by
      intro n
      apply Matrix.of.injective
      rw [GlobalTheory.SgInf.of_rmulM, hP, key n]
      simp only [mul_assoc]
    have hint : ∫⁻ n, φ (rmulM g₁ n) * (Eset k r z z' (n₁ * g₀ * n₂) R₀ y).indicator 1 (rmulM g₁ n) ∂lebN k r
        = ∫⁻ ν, φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν) ∂lebN k r := by
      calc _ = ∫⁻ n, (fun ν => φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν)) (e n) ∂lebN k r := by
            refine lintegral_congr fun n => ?_
            have hind : (Eset k r z z' (n₁ * g₀ * n₂) R₀ y).indicator (1 : Mt k r → ℝ≥0∞) (rmulM g₁ n) =
                (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A (e n)) := by
              by_cases h : rmulM g₁ n ∈ Eset k r z z' (n₁ * g₀ * n₂) R₀ y
              · simp only [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem n).1 h), Pi.one_apply]
              · have h' : rmulM A (e n) ∉ Eset k r z z' g₀ R₀ y := fun h' => h ((hmem n).2 h')
                first
                  | rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
                  | rw [Set.indicator_of_not_mem h, Set.indicator_of_not_mem h']
                  | simp [Set.indicator, h, h']
            dsimp only
            rw [hind, hpt n]
        _ = ∫⁻ ν, φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν) ∂((lebN k r).map e) :=
            (lintegral_map_equiv (fun ν => φ (P ν) * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM A ν)) e).symm
        _ = _ := by rw [he_map]
    have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
    rw [hint, ENNReal.ofReal_div_of_pos hs,
      ENNReal.le_div_iff_mul_le (Or.inl hs0) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm _ (ENNReal.ofReal s), ← lintegral_const_mul' (ENNReal.ofReal s) _ ENNReal.ofReal_ne_top]
    refine le_trans (le_of_eq ?_) hmain
    refine lintegral_congr fun ν => ?_
    simp only [mul_assoc]

end GlobalTheory.Amp.FibreVolumeGen
