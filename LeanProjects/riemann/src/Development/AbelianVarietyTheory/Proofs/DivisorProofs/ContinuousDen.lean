import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PBConjTranspose
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarInv

noncomputable section

open MeasureTheory
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1
open ReciprocityTheory.ChartRestriction.DS (PCoord pmat Jac dk muCD cPQ polarM)
open scoped NNReal ENNReal

namespace GlobalTheory.PsCo.Pc3.Polar

variable {n : ℕ}

def kap (ε : Fin n → Bool) (k : ReciprocityTheory.ChartRestriction.DS.S7.KG ε) : KG ε := k

theorem continuous_kap (ε : Fin n → Bool) : Continuous (kap ε) := continuous_id

theorem map_kap (ε : Fin n → Bool) : Measure.map (kap ε) (dk ε) = muK ε := by
  have hm : Measurable (kap ε) := (continuous_kap ε).measurable
  have h0 : ReciprocityTheory.ChartRestriction.DS.S7.muK ε Set.univ ≠ 0 :=
    (isOpen_univ.measure_pos (ReciprocityTheory.ChartRestriction.DS.S7.muK ε) ⟨1, Set.mem_univ _⟩).ne'
  have ht : ReciprocityTheory.ChartRestriction.DS.S7.muK ε Set.univ ≠ ⊤ := measure_ne_top _ _
  have key : ReciprocityTheory.ChartRestriction.DS.S7.muK ε =
      ReciprocityTheory.ChartRestriction.DS.S7.muK ε Set.univ • Measure.haarMeasure ⊤ := by
    simpa using Measure.haarMeasure_unique (ReciprocityTheory.ChartRestriction.DS.S7.muK ε) ⊤
  have hdk : dk ε = Measure.haarMeasure ⊤ := by
    unfold dk
    calc (ReciprocityTheory.ChartRestriction.DS.S7.muK ε Set.univ)⁻¹ • ReciprocityTheory.ChartRestriction.DS.S7.muK ε
        = (ReciprocityTheory.ChartRestriction.DS.S7.muK ε Set.univ)⁻¹ •
            (ReciprocityTheory.ChartRestriction.DS.S7.muK ε Set.univ • Measure.haarMeasure ⊤) := congrArg _ key
      _ = Measure.haarMeasure ⊤ := by rw [smul_smul, ENNReal.inv_mul_cancel h0 ht, one_smul]
  ext s hs
  rw [Measure.map_apply hm hs, hdk, Measure.haarMeasure_apply (hm hs)]
  unfold muK
  rw [Measure.haarMeasure_apply hs]
  simp only [TopologicalSpace.PositiveCompacts.coe_top]
  rw [Content.measure_apply _ MeasurableSet.univ, Content.measure_apply _ MeasurableSet.univ]
  rfl

theorem muK_inv (ε : Fin n → Bool) : (muK ε).IsInvInvariant := by
  rw [← map_kap ε]
  constructor
  show Measure.map Inv.inv (Measure.map (kap ε) (dk ε)) = Measure.map (kap ε) (dk ε)
  have hm : Measurable (kap ε) := (continuous_kap ε).measurable
  rw [Measure.map_map measurable_inv hm]
  have e1 : Measure.map (fun x => x⁻¹) (dk ε) = dk ε := by
    exact ReciprocityTheory.ChartRestriction.DS.CompactHaarProbability.dk_inv ε
  calc Measure.map (Inv.inv ∘ kap ε) (dk ε) = Measure.map (kap ε ∘ fun x => x⁻¹) (dk ε) := rfl
    _ = Measure.map (kap ε) (Measure.map (fun x => x⁻¹) (dk ε)) :=
        (Measure.map_map hm measurable_inv).symm
    _ = Measure.map (kap ε) (dk ε) := by rw [e1]

theorem muCD_inv (ε : Fin n → Bool) : (muCD ε).IsInvInvariant := by
  show (ENNReal.ofReal (cPQ ε) • ReciprocityTheory.ChartRestriction.DS.muPolar ε).IsInvInvariant
  constructor
  show Measure.map (fun x => x⁻¹) (ENNReal.ofReal (cPQ ε) • ReciprocityTheory.ChartRestriction.DS.muPolar ε) =
    ENNReal.ofReal (cPQ ε) • ReciprocityTheory.ChartRestriction.DS.muPolar ε
  rw [Measure.map_smul, ReciprocityTheory.ChartRestriction.DS.muPolar_inv ε]

def low (ε : Fin n → Bool) (B : Mode ε → ℂ) : PCoord ε → ℂ := fun x => pB ε B x.1.1 x.1.2

theorem pmat_low (ε : Fin n → Bool) (B : Mode ε → ℂ) : pmat (low ε B) = pB ε B := by
  funext a b
  simp only [pmat, low]
  split_ifs with h1 h2
  · rfl
  · have h := congrFun (congrFun (pB_conjTranspose ε B) a) b
    rw [Matrix.conjTranspose_apply] at h
    exact h
  · symm
    apply pB_ne
    by_contra hne
    rcases lt_trichotomy a b with h | h | h
    · exact h2 ⟨h, fun e => hne e.symm⟩
    · subst h
      exact hne rfl
    · exact h1 ⟨h, hne⟩

def lowL (ε : Fin n → Bool) : (Mode ε → ℂ) ≃ₗ[ℝ] (PCoord ε → ℂ) where
  toFun := low ε
  map_add' B C := by
    funext x
    simp only [low, pB, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c B := by
    funext x
    simp only [low, pB, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp
  invFun z := blkM ε (pmat z)
  left_inv B := by
    funext x
    obtain ⟨⟨a, b⟩, h⟩ := x
    simp only [blkM, pmat_low, pB]
    rw [dif_pos h]
  right_inv z := by
    funext x
    obtain ⟨⟨a, b⟩, h⟩ := x
    simp only [low, pB, blkM]
    split_ifs with h1 h2
    · simp only [pmat]
      rw [dif_pos h]
    · simp only [pmat]
      rw [dif_neg (fun h' => lt_asymm h'.1 h.1), dif_pos h, star_star]
    · exfalso
      have := h.2
      revert this h1 h2
      cases ε a <;> cases ε b <;> simp

theorem continuous_low (ε : Fin n → Bool) : Continuous (low ε) :=
  continuous_pi fun x => (continuous_apply x.1.2).comp ((continuous_apply x.1.1).comp (continuous_pB ε))

theorem low_neg (ε : Fin n → Bool) (B : Mode ε → ℂ) : low ε (-B) = -low ε B :=
  map_neg (lowL ε) B

theorem map_low (ε : Fin n → Bool) : ∃ c : ℝ≥0, c ≠ 0 ∧
    Measure.map (low ε) volume = c • (volume : Measure (PCoord ε → ℂ)) := by
  have : (Measure.map (low ε) (volume : Measure (Mode ε → ℂ))).IsAddHaarMeasure :=
    (lowL ε).toContinuousLinearEquiv.isAddHaarMeasure_map (volume : Measure (Mode ε → ℂ))
  exact ⟨Measure.addHaarScalarFactor (Measure.map (low ε) volume) volume,
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne',
    Measure.isAddLeftInvariant_eq_smul _ _⟩

theorem eB_neg (ε : Fin n → Bool) (B : Mode ε → ℂ) : eB ε (-B) = (eB ε B)⁻¹ := by
  have hp : pB ε (-B) = -pB ε B := by
    funext a b
    show pB ε (-B) a b = -(pB ε B a b)
    unfold pB
    split_ifs <;> simp
  have h1 := ((stEB n ε).2.2 (-B)).1
  have h2 := ((stEB n ε).2.2 B).2
  rw [hp, ← h2] at h1
  exact Subtype.ext (Units.ext h1)

def pol (ε : Fin n → Bool) (x : KG ε × (Mode ε → ℂ)) : UJ ε := x.1 * eB ε x.2

theorem continuous_pol (ε : Fin n → Bool) : Continuous (pol ε) :=
  (continuous_subtype_val.comp continuous_fst).mul ((stEB n ε).1.comp continuous_snd)

def den (ε : Fin n → Bool) (B : Mode ε → ℂ) : ℝ≥0 := (Jac (low ε B)).toNNReal

theorem continuous_den (ε : Fin n → Bool) : Continuous (den ε) :=
  continuous_real_toNNReal.comp ((ReciprocityTheory.ChartRestriction.DS.jac_continuous ε).comp (continuous_low ε))

def rho (ε : Fin n → Bool) : Measure (KG ε × (Mode ε → ℂ)) :=
  (muK ε).prod (volume.withDensity fun B => (den ε B : ℝ≥0∞))

theorem map_pol (ε : Fin n → Bool) : ∃ c : ℝ≥0, c ≠ 0 ∧ muCD ε = c • Measure.map (pol ε) (rho ε) := by
  obtain ⟨c0, hc0, hlow⟩ := map_low ε
  have hl : Measurable (low ε) := (continuous_low ε).measurable
  have hJm : Measurable (fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) :=
    ENNReal.measurable_ofReal.comp (ReciprocityTheory.ChartRestriction.DS.jac_continuous ε).measurable
  have hden : Measure.map (low ε) (volume.withDensity fun B => (den ε B : ℝ≥0∞)) =
      c0 • volume.withDensity (fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) := by
    rw [ENNReal.smul_def] at hlow ⊢
    ext s hs
    have hL := congrArg
      (fun m : Measure (PCoord ε → ℂ) => ∫⁻ z, s.indicator (fun z => ENNReal.ofReal (Jac z)) z ∂m) hlow
    simp only [lintegral_smul_measure, smul_eq_mul] at hL
    rw [lintegral_map (hJm.indicator hs) hl, lintegral_indicator hs] at hL
    rw [Measure.map_apply hl hs, withDensity_apply _ (hl hs), Measure.smul_apply, withDensity_apply _ hs,
      smul_eq_mul, ← hL, ← lintegral_indicator (hl hs)]
    refine lintegral_congr fun B => ?_
    by_cases hB : low ε B ∈ s
    · simp [Set.indicator, hB, den, ENNReal.ofReal]
    · simp [Set.indicator, hB]
  have hκ : Measurable (Prod.map (kap ε) (id : (Mode ε → ℂ) → (Mode ε → ℂ))) :=
    (continuous_kap ε).measurable.prodMap measurable_id
  have hψ : Measurable (Prod.map (id : ReciprocityTheory.ChartRestriction.DS.S7.KG ε → ReciprocityTheory.ChartRestriction.DS.S7.KG ε) (low ε)) :=
    measurable_id.prodMap hl
  have hprod : Measure.map (Prod.map id (low ε)) ((dk ε).prod (volume.withDensity fun B => (den ε B : ℝ≥0∞))) =
      (dk ε).prod (c0 • volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) := by
    rw [← Measure.map_prod_map _ _ measurable_id hl, Measure.map_id, hden]
  have hmk : Measure.map (Prod.map (kap ε) id) ((dk ε).prod (volume.withDensity fun B => (den ε B : ℝ≥0∞))) =
      rho ε := by
    rw [← Measure.map_prod_map _ _ (continuous_kap ε).measurable measurable_id, Measure.map_id, map_kap]
    rfl
  have hpt : (fun x => polarM (Prod.map id (low ε) x)) =
      fun x => Formalism.MainNotions.S.umat (pol ε (Prod.map (kap ε) id x)) := by
    funext x
    obtain ⟨k, B⟩ := x
    show polarM (k, low ε B) = Formalism.MainNotions.S.umat ((kap ε k : UJ ε) * eB ε B)
    rw [show Formalism.MainNotions.S.umat ((kap ε k : UJ ε) * eB ε B) = toM (kap ε k : UJ ε) * toM (eB ε B) from rfl,
      toM_eB, ← pmat_low ε B]
    rfl
  have hpm : Measurable (pol ε) := (continuous_pol ε).measurable
  have hpolC : Continuous (Y := Fin n → Fin n → ℂ) (polarM (ε := ε)) :=
    ReciprocityTheory.ChartRestriction.DS.polarM_continuous ε
  have hpolM : Measurable (polarM (ε := ε)) := hpolC.measurable
  have hce : Topology.IsClosedEmbedding (X := UJ ε) (Y := Fin n → Fin n → ℂ) (fun g => Formalism.MainNotions.S.umat g) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1
  have humP : MeasurableEmbedding (α := UJ ε) (β := Fin n → Fin n → ℂ) (fun g => Formalism.MainNotions.S.umat g) :=
    hce.measurableEmbedding
  have hum : MeasurableEmbedding (fun g : UJ ε => Formalism.MainNotions.S.umat g) := humP
  have hmain : Measure.map polarM
      ((dk ε).prod (c0 • volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z))) =
      Measure.map (fun g : UJ ε => Formalism.MainNotions.S.umat g) (Measure.map (pol ε) (rho ε)) := by
    rw [← hprod, ← hmk, Measure.map_map hpolM hψ, Measure.map_map hpm hκ,
      Measure.map_map hum.measurable (hpm.comp hκ)]
    exact congrArg (fun F => Measure.map F ((dk ε).prod (volume.withDensity fun B => (den ε B : ℝ≥0∞)))) hpt
  have h2 : Measure.map polarM ((dk ε).prod (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z))) =
      (c0 : ℝ≥0∞)⁻¹ • Measure.map (fun g : UJ ε => Formalism.MainNotions.S.umat g) (Measure.map (pol ε) (rho ε)) := by
    rw [← hmain, ENNReal.smul_def, Measure.prod_smul_right, Measure.map_smul, smul_smul,
      ENNReal.inv_mul_cancel (by exact_mod_cast hc0) ENNReal.coe_ne_top, one_smul]
  refine ⟨(cPQ ε).toNNReal * c0⁻¹,
    mul_ne_zero (Real.toNNReal_pos.mpr (ReciprocityTheory.ChartRestriction.DS.cPQ_pos ε)).ne' (inv_ne_zero hc0), ?_⟩
  unfold muCD ReciprocityTheory.ChartRestriction.DS.muPolarMat
  erw [h2]
  ext s hs
  rw [Measure.smul_apply]
  erw [humP.comap_apply]
  rw [Measure.smul_apply ((cPQ ε).toNNReal * c0⁻¹)]
  erw [Measure.smul_apply ((c0 : ℝ≥0∞)⁻¹), humP.map_apply, humP.injective.preimage_image]
  simp only [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul, ENNReal.coe_inv hc0, mul_assoc]
  rfl

theorem left (ε : Fin n → Bool) (μ : Measure (UJ ε)) (c : ℝ≥0) (hc : c ≠ 0) [IsFiniteMeasureOnCompacts μ]
    (h : μ = c • Measure.map (pol ε) (rho ε)) (f : UJ ε → ℂ) (hf : Continuous f) (hs : HasCompactSupport f) :
    ∫ g, f g ∂μ = ∫ B, (((c : ℝ) * den ε B : ℝ) : ℂ) * ∫ k : KG ε, f (k * eB ε B) ∂(muK ε) := by
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hs
  have hcne : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc
  have hpm : Measurable (pol ε) := (continuous_pol ε).measurable
  have hfm : Integrable f (Measure.map (pol ε) (rho ε)) := by
    rw [h, ENNReal.smul_def] at hfi
    exact (integrable_smul_measure hcne ENNReal.coe_ne_top).mp hfi
  have hfp : Integrable (fun x => f (pol ε x)) (rho ε) :=
    (integrable_map_measure hf.aestronglyMeasurable hpm.aemeasurable).mp hfm
  rw [h, integral_smul_nnreal_measure, integral_map hpm.aemeasurable hf.aestronglyMeasurable]
  unfold rho at hfp ⊢
  rw [integral_prod_symm _ hfp, integral_withDensity_eq_integral_smul (continuous_den ε).measurable,
    NNReal.smul_def, ← integral_smul]
  congr 1
  funext B
  simp only [NNReal.smul_def, Complex.real_smul, pol]
  push_cast
  ring

end GlobalTheory.PsCo.Pc3.Polar

namespace GlobalTheory.PsCo.Pc3

open Polar

theorem stPolar : StPolar := by
  intro n ε μ _
  have := ReciprocityTheory.ChartRestriction.DS.muCD_isHaar ε
  obtain ⟨c, hc, hcd⟩ := map_pol ε
  have ha : μ = Measure.haarScalarFactor μ (muCD ε) • muCD ε :=
    Measure.isMulLeftInvariant_eq_smul μ (muCD ε)
  have hapos : 0 < Measure.haarScalarFactor μ (muCD ε) :=
    Measure.haarScalarFactor_pos_of_isHaarMeasure μ (muCD ε)
  set a := Measure.haarScalarFactor μ (muCD ε) with ha_def
  have hne : a * c ≠ 0 := mul_ne_zero hapos.ne' hc
  have hμ : μ = (a * c) • Measure.map (pol ε) (rho ε) := by rw [ha, hcd, smul_smul]
  have hinv : μ.IsInvInvariant := by
    constructor
    show Measure.map Inv.inv μ = μ
    rw [ha, Measure.map_smul]
    rw [show Measure.map Inv.inv (muCD ε) = muCD ε from (muCD_inv ε).inv_eq_self]
  have hJ : ∀ B, den ε (-B) = den ε B := fun B => by
    simp only [den, low_neg, ReciprocityTheory.ChartRestriction.DS.jac_neg]
  have := muK_inv ε
  refine ⟨fun B => ((a * c : ℝ≥0) : ℝ) * den ε B, ?_, ?_, fun f hf hs => ⟨?_, ?_⟩⟩
  · exact continuous_const.mul (NNReal.continuous_coe.comp (continuous_den ε))
  · have hj : 0 < Jac (low ε 0) := by
      exact ReciprocityTheory.ChartRestriction.DS.fdph_jac_pos _
    have hd : (0 : ℝ) < den ε 0 := NNReal.coe_pos.mpr (Real.toNNReal_pos.mpr hj)
    exact mul_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hne)) hd
  · exact left ε μ (a * c) hne hμ f hf hs
  · have hg : ∀ B, ∫ k : KG ε, f (((k : UJ ε) * eB ε B)⁻¹) ∂(muK ε) =
        ∫ k : KG ε, f (eB ε (-B) * k) ∂(muK ε) := by
      intro B
      rw [eB_neg]
      have e := integral_inv_eq_self (fun k : KG ε => f ((eB ε B)⁻¹ * (k : UJ ε))) (muK ε)
      rw [← e]
      congr 1
    have hneg := Measure.integral_comp_smul (volume : Measure (Mode ε → ℂ))
      (fun B => ((((a * c : ℝ≥0) : ℝ) * den ε B : ℝ) : ℂ) * ∫ k : KG ε, f (eB ε B * k) ∂(muK ε)) (-1)
    simp only [neg_one_smul, abs_inv, abs_pow, abs_neg, abs_one, one_pow, inv_one, one_smul] at hneg
    calc ∫ g, f g ∂μ = ∫ g, f g⁻¹ ∂μ := (integral_inv_eq_self f μ).symm
      _ = ∫ B, ((((a * c : ℝ≥0) : ℝ) * den ε B : ℝ) : ℂ) *
            ∫ k : KG ε, f (((k : UJ ε) * eB ε B)⁻¹) ∂(muK ε) :=
          left ε μ (a * c) hne hμ (fun g => f g⁻¹) (hf.comp continuous_inv)
            (hs.comp_homeomorph (Homeomorph.inv _))
      _ = ∫ B, ((((a * c : ℝ≥0) : ℝ) * den ε (-B) : ℝ) : ℂ) *
            ∫ k : KG ε, f (eB ε (-B) * k) ∂(muK ε) := by
          simp only [hg, hJ]
      _ = ∫ B, ((((a * c : ℝ≥0) : ℝ) * den ε B : ℝ) : ℂ) * ∫ k : KG ε, f (eB ε B * k) ∂(muK ε) :=
          hneg

end GlobalTheory.PsCo.Pc3
