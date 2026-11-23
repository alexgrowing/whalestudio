import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InitialStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.RgLineFormula

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S

def slab (s : ℝ) : ℝ≥0∞ := (Set.Ico (0 : ℝ) 1).indicator (fun _ => 1) s

theorem measurable_slab : Measurable slab := by
  exact measurable_const.indicator measurableSet_Ico

theorem lintegral_slab (s : ℝ) : ∫⁻ t : ℝ, slab (s - t) = 1 := by
  have h1 : ∫⁻ t : ℝ, slab (s - t) = ∫⁻ t : ℝ, slab t := lintegral_sub_left_eq_self slab s
  rw [h1]
  unfold slab
  rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico]
  simp

section Abstract

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

theorem inner_formula (μM : Measure G) [SFinite μM] (S P : Set G) (a : ℝ → G) (δ : G → ℝ≥0∞) (T : G → ℝ) (ρ : ℝ)
    (ha : Measurable a) (hδ : Measurable δ) (hT : Measurable T) (hadd : ∀ s t, a (s + t) = a s * a t)
    (hinv : ∀ t, μM.map (· * a t) = μM)
    (hmod : ∀ m ∈ S, ∀ t, δ (m * a t) = δ m * ENNReal.ofReal (Real.exp (2 * ρ * t)))
    (htime : ∀ x ∈ P, ∀ t, T (x * a t) = T x + t)
    (F : G → ℝ≥0∞) (hF : Measurable F) (u : G) (hS : ∀ᵐ m ∂μM, m ∈ S) (hP : ∀ᵐ m ∂μM, u * m ∈ P) :
    ∫⁻ m, δ m * (slab (T (u * m)) * ∫⁻ t : ℝ, F (u * m * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t))) ∂μM =
      ∫⁻ m, δ m * F (u * m) ∂μM := by
  have hEm : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (2 * ρ * t)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hsl : Measurable fun m : G => slab (T (u * m)) :=
    measurable_slab.comp (hT.comp (measurable_const_mul u))
  have ha0 : a 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hEinv : ∀ t : ℝ, ENNReal.ofReal (Real.exp (2 * ρ * -t)) * ENNReal.ofReal (Real.exp (2 * ρ * t)) = 1 := by
    intro t
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  have step1 : ∫⁻ m, δ m * (slab (T (u * m)) *
        ∫⁻ t : ℝ, F (u * m * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t))) ∂μM
      = ∫⁻ m, (∫⁻ t : ℝ, δ m * (slab (T (u * m)) *
        (F (u * m * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t))))) ∂μM := by
    refine lintegral_congr fun m => ?_
    have hm : Measurable fun t : ℝ => F (u * m * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t)) :=
      (hF.comp (measurable_const.mul ha)).mul hEm
    rw [lintegral_const_mul _ (hm.const_mul _), lintegral_const_mul _ hm]
  have hH : Measurable (Function.uncurry fun (m : G) (t : ℝ) => δ m * (slab (T (u * m)) *
        (F (u * m * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t))))) :=
    (hδ.comp measurable_fst).mul ((hsl.comp measurable_fst).mul
      ((hF.comp (((measurable_const_mul u).comp measurable_fst).mul (ha.comp measurable_snd))).mul
        (hEm.comp measurable_snd)))
  have hK : Measurable (Function.uncurry fun (m : G) (t : ℝ) => δ m * (F (u * m) * slab (T (u * m) - t))) :=
    (hδ.comp measurable_fst).mul ((hF.comp ((measurable_const_mul u).comp measurable_fst)).mul
      (measurable_slab.comp ((hT.comp ((measurable_const_mul u).comp measurable_fst)).sub measurable_snd)))
  have step2 : ∀ t : ℝ, ∫⁻ m, δ m * (slab (T (u * m)) *
        (F (u * m * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t)))) ∂μM
      = ∫⁻ m, δ m * (F (u * m) * slab (T (u * m) - t)) ∂μM := by
    intro t
    have hg : Measurable fun m : G => δ m * (slab (T (u * m)) *
        (F (u * m * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t)))) :=
      hδ.mul (hsl.mul ((hF.comp ((measurable_const_mul u).mul_const (a t))).mul measurable_const))
    conv_lhs => rw [← hinv (-t)]
    rw [lintegral_map hg (measurable_mul_const (a (-t)))]
    refine lintegral_congr_ae ?_
    filter_upwards [hS, hP] with m hm hp
    have e1 := hmod m hm (-t)
    have e2 := htime (u * m) hp (-t)
    have e3 : u * (m * a (-t)) * a t = u * m := by
      rw [mul_assoc, mul_assoc, ← hadd, neg_add_cancel, ha0, mul_one]
    rw [e1, e3, ← mul_assoc u m, e2, ← sub_eq_add_neg]
    calc δ m * ENNReal.ofReal (Real.exp (2 * ρ * -t)) *
          (slab (T (u * m) - t) * (F (u * m) * ENNReal.ofReal (Real.exp (2 * ρ * t))))
        = δ m * (F (u * m) * slab (T (u * m) - t)) *
          (ENNReal.ofReal (Real.exp (2 * ρ * -t)) * ENNReal.ofReal (Real.exp (2 * ρ * t))) := by ring
      _ = δ m * (F (u * m) * slab (T (u * m) - t)) := by rw [hEinv, mul_one]
  rw [step1, lintegral_lintegral_swap hH.aemeasurable]
  simp_rw [step2]
  rw [← lintegral_lintegral_swap hK.aemeasurable]
  refine lintegral_congr fun m => ?_
  have hs : Measurable fun t : ℝ => slab (T (u * m) - t) :=
    measurable_slab.comp (measurable_const.sub measurable_id)
  rw [lintegral_const_mul _ (hs.const_mul _), lintegral_const_mul _ hs, lintegral_slab, mul_one]

theorem ae_mul_mem (Q : Subgroup G) (hQ : MeasurableSet (Q : Set G)) (ν : Measure Q) (μN μM : Measure G) [SFinite μN]
    [SFinite μM] (S : Set G) (δ : G → ℝ≥0∞) (hδ : Measurable δ) (hδ0 : ∀ m ∈ S, δ m ≠ 0) (hS : ∀ᵐ m ∂μM, m ∈ S)
    (c : ℝ≥0∞) (hc0 : c ≠ 0)
    (hc : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ x, F x ∂(ν.map Subtype.val) = c * ∫⁻ u, ∫⁻ m, δ m * F (u * m) ∂μM ∂μN) :
    ∀ᵐ u ∂μN, ∀ᵐ m ∂μM, u * m ∈ Q := by
  have hF : Measurable ((Q : Set G)ᶜ.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hQ.compl
  have h := hc _ hF
  have hL : ∫⁻ x, (Q : Set G)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x ∂(ν.map Subtype.val) = 0 := by
    rw [lintegral_indicator_const hQ.compl, Measure.map_apply measurable_subtype_coe hQ.compl, one_mul]
    have he : (Subtype.val ⁻¹' ((Q : Set G)ᶜ) : Set Q) = ∅ := by
      ext x
      simp
    rw [he, measure_empty]
  rw [hL] at h
  have h2 : ∫⁻ u, ∫⁻ m, δ m * (Q : Set G)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (u * m) ∂μM ∂μN = 0 := by
    rcases mul_eq_zero.mp h.symm with h0 | h0
    · exact absurd h0 hc0
    · exact h0
  have hmeas : Measurable fun u : G => ∫⁻ m, δ m * (Q : Set G)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (u * m) ∂μM :=
    Measurable.lintegral_prod_right
      (f := fun (u m : G) => δ m * (Q : Set G)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (u * m))
      ((hδ.comp measurable_snd).mul (hF.comp (measurable_fst.mul measurable_snd)))
  have h3 := (lintegral_eq_zero_iff' hmeas.aemeasurable).mp h2
  filter_upwards [h3] with u hu
  have hu' : ∫⁻ m, δ m * (Q : Set G)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (u * m) ∂μM = 0 := hu
  have hm : Measurable fun m : G => δ m * (Q : Set G)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (u * m) :=
    hδ.mul (hF.comp (measurable_const_mul u))
  have h4 := (lintegral_eq_zero_iff' hm.aemeasurable).mp hu'
  filter_upwards [h4, hS] with m hm0 hmS
  have hm0' : δ m * (Q : Set G)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (u * m) = 0 := hm0
  by_contra hnot
  have hind : (Q : Set G)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (u * m) = 1 :=
    Set.indicator_of_mem (show u * m ∈ (Q : Set G)ᶜ from hnot) _
  rw [hind, mul_one] at hm0'
  exact hδ0 m hmS hm0'

theorem slab_formula (Q : Subgroup G) (hQ : MeasurableSet (Q : Set G)) (ν : Measure Q) (μN μM : Measure G) [SFinite μN]
    [SFinite μM] (S : Set G) (a : ℝ → G) (δ : G → ℝ≥0∞) (T : G → ℝ) (ρ : ℝ)
    (ha : Measurable a) (hδ : Measurable δ) (hT : Measurable T) (hadd : ∀ s t, a (s + t) = a s * a t)
    (hinv : ∀ t, μM.map (· * a t) = μM)
    (hmod : ∀ m ∈ S, ∀ t, δ (m * a t) = δ m * ENNReal.ofReal (Real.exp (2 * ρ * t)))
    (hδ0 : ∀ m ∈ S, δ m ≠ 0) (hS : ∀ᵐ m ∂μM, m ∈ S)
    (htime : ∀ x ∈ Q, ∀ t, T (x * a t) = T x + t)
    (c : ℝ≥0∞) (hc0 : c ≠ 0)
    (hc : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ x, F x ∂(ν.map Subtype.val) = c * ∫⁻ u, ∫⁻ m, δ m * F (u * m) ∂μM ∂μN)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x in {x : Q | T x ∈ Set.Ico 0 1},
        (∫⁻ t : ℝ, F ((x : G) * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t))) ∂ν =
      c * ∫⁻ u, ∫⁻ m, δ m * F (u * m) ∂μM ∂μN := by
  have hEm : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (2 * ρ * t)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hg : Measurable fun y : G => ∫⁻ t : ℝ, F (y * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t)) :=
    Measurable.lintegral_prod_right
      (f := fun (y : G) (t : ℝ) => F (y * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t)))
      ((hF.comp (measurable_fst.mul (ha.comp measurable_snd))).mul (hEm.comp measurable_snd))
  have hG : Measurable fun y : G =>
      slab (T y) * ∫⁻ t : ℝ, F (y * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t)) :=
    (measurable_slab.comp hT).mul hg
  have hset : MeasurableSet {x : Q | T x ∈ Set.Ico (0 : ℝ) 1} :=
    (hT.comp measurable_subtype_coe) measurableSet_Ico
  have e1 : ∫⁻ x in {x : Q | T x ∈ Set.Ico 0 1},
        (∫⁻ t : ℝ, F ((x : G) * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t))) ∂ν
      = ∫⁻ y, slab (T y) * (∫⁻ t : ℝ, F (y * a t) * ENNReal.ofReal (Real.exp (2 * ρ * t)))
          ∂(ν.map Subtype.val) := by
    rw [lintegral_map hG measurable_subtype_coe, ← lintegral_indicator hset]
    refine lintegral_congr fun x => ?_
    by_cases hx : T x ∈ Set.Ico (0 : ℝ) 1
    · rw [Set.indicator_of_mem (show x ∈ {x : Q | T x ∈ Set.Ico (0 : ℝ) 1} from hx)]
      simp [slab, hx]
    · rw [Set.indicator_of_notMem (show x ∉ {x : Q | T x ∈ Set.Ico (0 : ℝ) 1} from hx)]
      simp [slab, hx]
  rw [e1, hc _ hG]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mul_mem Q hQ ν μN μM S δ hδ hδ0 hS c hc0 hc] with u hu
  exact inner_formula μM S (Q : Set G) a δ T ρ ha hδ hT hadd hinv hmod htime F hF u hS hu

end Abstract

variable {n : ℕ} {ε : Fin n → Bool}

theorem lineFormula : Fub2 → LineFacts → PSubEq → LineFormula := by
  intro hFub hLF hPS
  unfold LineFormula
  intro n ε A ν τ hA hν hτc hτ
  obtain ⟨μN, μM, hN, hM, hMae, hinvM, ⟨κ, hκ0, hκT, hG⟩, hpar⟩ := hFub n ε A hA
  obtain ⟨a, τ', hac, -, hau, hadd, hamem, hacomm, hmod, -⟩ := hLF n ε A hA
  obtain ⟨c, hc0, hcT, hc⟩ := hpar ν hν
  have hPS' := hPS n ε A hA
  change ℝ → ↥(ReciprocityTheory.ChartRestriction.DS.S7.UJ ε) at a
  change Measure ↥(ReciprocityTheory.ChartRestriction.DS.S7.UJ ε) at μN μM
  haveI : SFinite μN := hN
  haveI : SFinite μM := hM
  have hmulM : ∀ (x : ↥(ReciprocityTheory.ChartRestriction.DS.S7.UJ ε)) (t : ℝ),
      ReciprocityTheory.ChartRestriction.DS.S7.toM (x * a t) = ReciprocityTheory.ChartRestriction.DS.S7.toM x * CompanionTheory.RgExh.Dec.L.aT A t := by
    intro x t
    rw [CompanionTheory.RgExh.Dec.L.aT, ← hau t]
    rfl
  have h1N : (1 : ↥(Formalism.REAL.UJ ε)) ∈ GlobalTheory.FlagMeas.flagN ε (W A) := by
    simp only [GlobalTheory.FlagMeas.flagN, Set.mem_setOf_eq]
    constructor
    · intro i y _
      simp [Formalism.MainNotions.S.uMat]
    · intro y _
      simp [Formalism.MainNotions.S.uMat]
  have hat : ∀ t : ℝ, a t ∈ PSub ε A := fun t => (hPS' (a t)).mpr ⟨1, h1N, a t, hamem t, (one_mul _).symm⟩
  have htime : ∀ x ∈ PSub ε A, ∀ t : ℝ, τ (x * a t) = τ x + t := by
    intro x hx t
    exact hτ ⟨x, hx⟩ t ⟨x * a t, (PSub ε A).mul_mem hx (hat t)⟩ (hmulM x t)
  have hinv : ∀ t : ℝ, μM.map (· * a t) = μM :=
    fun t => hinvM (a t) (hamem t) (fun m hm => hacomm t m hm)
  have hS : ∀ᵐ m ∂μM, m ∈ GlobalTheory.FlagMeas.flagM ε (W A) := ae_iff.mpr hMae
  have hQ : MeasurableSet ((PSub ε A : Set ↥(ReciprocityTheory.ChartRestriction.DS.S7.UJ ε))) :=
    (GlobalTheory.CompanionTheory.ParabolicHaar.isClosed_pSub ε A).measurableSet
  refine ⟨κ * c⁻¹, mul_ne_zero hκ0 (ENNReal.inv_ne_zero.mpr hcT),
    ENNReal.mul_ne_top hκT (ENNReal.inv_ne_top.mpr hc0), fun F hFm hFK => ?_⟩
  have hK : ∀ g k : ↥(Formalism.REAL.UJ ε), k ∈ Formalism.REAL.KG ε →
      F (ReciprocityTheory.ChartRestriction.DS.S7.toM (g * k)) = F (ReciprocityTheory.ChartRestriction.DS.S7.toM g) :=
    fun g k hk => hFK g ⟨k, hk⟩
  have h1 := hG (fun g => F (ReciprocityTheory.ChartRestriction.DS.S7.toM g)) hFm hK
  have h2 := slab_formula (PSub ε A) hQ ν μN μM (GlobalTheory.FlagMeas.flagM ε (W A)) a (modA A) τ (rhoA A)
    hac.measurable (GlobalTheory.CompanionTheory.RgStart.measurable_modA A) hτc.measurable hadd hinv hmod
    (fun m hm => GlobalTheory.CompanionTheory.RgStart.modA_ne_zero A hm) hS htime c hc0 hc
    (fun g => F (ReciprocityTheory.ChartRestriction.DS.S7.toM g)) hFm
  have h3 : (∫⁻ x in {x : ↥(PSub ε A) | τ ↑x ∈ Set.Ico 0 1},
        (∫⁻ t : ℝ, F (ReciprocityTheory.ChartRestriction.DS.S7.toM (x : ↥(ReciprocityTheory.ChartRestriction.DS.S7.UJ ε)) * CompanionTheory.RgExh.Dec.L.aT A t) *
          ENNReal.ofReal (Real.exp (2 * rhoA A * t))) ∂ν)
      = ∫⁻ x in {x : ↥(PSub ε A) | τ ↑x ∈ Set.Ico 0 1},
        (∫⁻ t : ℝ, F (ReciprocityTheory.ChartRestriction.DS.S7.toM ((x : ↥(ReciprocityTheory.ChartRestriction.DS.S7.UJ ε)) * a t)) *
          ENNReal.ofReal (Real.exp (2 * rhoA A * t))) ∂ν := by
    simp only [hmulM]
  clear hpar hinvM hmod hacomm hamem hadd hau hPS' hτ hMae hinv hS htime hat h1N hmulM hK hQ hG
  refine h1.trans ?_
  rw [h3.trans h2, mul_assoc κ, ← mul_assoc c⁻¹, ENNReal.inv_mul_cancel hc0 hcT, one_mul]
  all_goals rfl

end GlobalTheory.CompanionTheory.RgLineFormula
