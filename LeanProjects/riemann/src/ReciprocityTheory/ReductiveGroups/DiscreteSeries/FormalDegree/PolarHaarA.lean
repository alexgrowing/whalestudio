import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable

noncomputable section

open Finset Matrix MeasureTheory Topology
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma fdph_muK_univ_ne_zero (ε : Fin n → Bool) : muK ε Set.univ ≠ 0 := by
  exact isOpen_univ.measure_ne_zero (muK ε) Set.univ_nonempty

lemma fdph_muK_univ_ne_top (ε : Fin n → Bool) : muK ε Set.univ ≠ ⊤ := by
  exact (isCompact_univ.measure_lt_top (μ := muK ε)).ne

instance fdph_dk_finite (ε : Fin n → Bool) : IsFiniteMeasure (dk ε) := by
  refine ⟨?_⟩
  rw [dk, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr (fdph_muK_univ_ne_zero ε)))
    isCompact_univ.measure_lt_top

instance fdph_dk_openPos (ε : Fin n → Bool) : Measure.IsOpenPosMeasure (dk ε) := by
  unfold dk
  exact Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr (fdph_muK_univ_ne_top ε))

lemma fdph_shc_pos (u : ℝ) : 0 < shc u := by
  unfold shc
  split_ifs with h
  · exact one_pos
  · rcases lt_or_gt_of_ne h with h' | h'
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr h') h'
    · exact div_pos (Real.sinh_pos_iff.mpr h') h'

lemma fdph_jac_pos {ε : Fin n → Bool} (z : PCoord ε → ℂ) : 0 < Jac z := by
  unfold Jac
  exact Finset.prod_pos fun a _ => Finset.prod_pos fun b _ => fdph_shc_pos _

abbrev fdphNu (ε : Fin n → Bool) : Measure (PCoord ε → ℂ) :=
  (volume : Measure (PCoord ε → ℂ)).withDensity fun z => ENNReal.ofReal (Jac z)

instance fdph_nu_openPos (ε : Fin n → Bool) : Measure.IsOpenPosMeasure (fdphNu ε) := by
  refine ⟨fun U hU hne => ?_⟩
  have hm : Measurable fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z) :=
    ENNReal.measurable_ofReal.comp (jac_continuous ε).measurable
  rw [Ne, fdphNu, withDensity_apply_eq_zero hm]
  have hu : {x : PCoord ε → ℂ | ENNReal.ofReal (Jac x) ≠ 0} = Set.univ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact fdph_jac_pos x
  rw [hu, Set.univ_inter]
  exact hU.measure_ne_zero volume hne

instance fdph_nu_finCpt (ε : Fin n → Bool) : IsFiniteMeasureOnCompacts (fdphNu ε) := by
  refine ⟨fun K hK => ?_⟩
  rw [fdphNu, withDensity_apply' _ K]
  exact setLIntegral_lt_top_of_isCompact hK.measure_lt_top.ne hK (f := fun z => (Jac z).toNNReal)
    (continuous_real_toNNReal.comp (jac_continuous ε))

def fdphPhi (ε : Fin n → Bool) (kz : KG ε × (PCoord ε → ℂ)) : UJ ε :=
  ⟨⟨polarM kz, Jm ε * (polarM kz)ᴴ * Jm ε,
    mul_eq_one_comm.mp (left_inv_of_inUJ ε _ (polarM_inUJ kz)), left_inv_of_inUJ ε _ (polarM_inUJ kz)⟩,
    polarM_inUJ kz⟩

lemma fdph_toM_phi (ε : Fin n → Bool) (kz : KG ε × (PCoord ε → ℂ)) : toM (fdphPhi ε kz) = polarM kz := rfl

lemma fdph_phi_continuous (ε : Fin n → Bool) : Continuous (fdphPhi ε) := by
  unfold fdphPhi
  have hexp : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp M) := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    exact NormedSpace.exp_continuous
  have htoMK : Continuous (fun k : KG ε => toMK k) := by
    fun_prop
  have hpmat : Continuous (fun z : PCoord ε → ℂ => pmat z) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    by_cases h : b < a ∧ ε a ≠ ε b
    · simp only [pmat, dif_pos h]
      exact continuous_apply _
    · by_cases h' : a < b ∧ ε b ≠ ε a
      · simp only [pmat, dif_neg h, dif_pos h']
        exact (continuous_apply _).star
      · simp only [pmat, dif_neg h, dif_neg h']
        exact continuous_const
  have hpol : Continuous (fun kz : KG ε × (PCoord ε → ℂ) => polarM kz) := by
    unfold polarM
    exact (htoMK.comp continuous_fst).matrix_mul (hexp.comp (hpmat.comp continuous_snd))
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  exact ⟨hpol, (continuous_const.matrix_mul hpol.matrix_conjTranspose).matrix_mul continuous_const⟩

lemma fdph_preimage (ε : Fin n → Bool) (S : Set (UJ ε)) :
    Set.preimage (β := Fin n → Fin n → ℂ) polarM (Set.image (β := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) S) =
      fdphPhi ε ⁻¹' S := by
  ext kz
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨g, hg, hgeq⟩
    have hge : g = fdphPhi ε kz :=
      Subtype.ext (Units.ext (hgeq.trans (fdph_toM_phi ε kz).symm))
    rw [← hge]
    exact hg
  · intro h
    exact ⟨fdphPhi ε kz, h, fdph_toM_phi ε kz⟩

lemma fdph_apply (ε : Fin n → Bool) {S : Set (UJ ε)} (hS : MeasurableSet S) :
    muPolar ε S = ((dk ε).prod (fdphNu ε)) (fdphPhi ε ⁻¹' S) := by
  have hC : IsClosedEmbedding (Y := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) := isClosedEmbedding_toM ε
  have hE : MeasurableEmbedding (β := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) := hC.measurableEmbedding
  have hPc : Continuous (Y := Fin n → Fin n → ℂ) (polarM (ε := ε)) := (polarM_isClosedEmbedding ε).continuous
  have hP : Measurable (β := Fin n → Fin n → ℂ) (polarM (ε := ε)) := hPc.measurable
  unfold muPolar muPolarMat
  rw [hE.comap_apply, Measure.map_apply hP (hE.measurableSet_image' hS), fdph_preimage]

theorem fdph_isHaar_of (ε : Fin n → Bool)
    (hR : ∀ g : UJ ε, Measure.map (fun x => x * g) (muPolar ε) = muPolar ε)
    (hI : Measure.map (fun x : UJ ε => x⁻¹) (muPolar ε) = muPolar ε) : (muPolar ε).IsHaarMeasure := by
  have hL : (muPolar ε).IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    have e : (fun x : UJ ε => g * x) = (fun x => x⁻¹) ∘ ((fun x => x * g⁻¹) ∘ (fun x => x⁻¹)) := by
      funext x; simp [_root_.mul_inv_rev]
    rw [e, ← Measure.map_map measurable_inv ((measurable_mul_const _).comp measurable_inv),
      ← Measure.map_map (measurable_mul_const _) measurable_inv, hI, hR g⁻¹, hI]
  have hF : IsFiniteMeasureOnCompacts (muPolar ε) := by
    refine ⟨fun K hK => ?_⟩
    rw [fdph_apply ε hK.isClosed.measurableSet, ← fdph_preimage]
    exact ((polarM_isClosedEmbedding ε).isCompact_preimage (hK.image (continuous_toM ε))).measure_lt_top
  have hO : Measure.IsOpenPosMeasure (muPolar ε) := by
    refine ⟨fun U hU hne => ?_⟩
    rw [fdph_apply ε hU.measurableSet]
    obtain ⟨g, hg⟩ := hne
    obtain ⟨kz, hkz⟩ := polarM_surj (toM g) g.2
    have : fdphPhi ε kz = g := (isClosedEmbedding_toM ε).injective (by rw [fdph_toM_phi]; exact hkz)
    exact (hU.preimage (fdph_phi_continuous ε)).measure_ne_zero _ ⟨kz, by rw [Set.mem_preimage, this]; exact hg⟩
  exact { toIsFiniteMeasureOnCompacts := hF, toIsMulLeftInvariant := hL, toIsOpenPosMeasure := hO }

end ReciprocityTheory.ChartRestriction.DS
