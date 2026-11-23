import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntMuCD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem polarInv_pmat_neg {ε : Fin n → Bool} (z : PCoord ε → ℂ) : pmat (-z) = -pmat z := by
  ext a b
  simp only [pmat, Matrix.neg_apply, Pi.neg_apply]
  split_ifs <;> simp [star_neg]

theorem polarInv_Jm_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) : Jm ε * pmat z * Jm ε = -pmat z := by
  ext a b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
  by_cases hab : ε a = ε b
  · have h0 : pmat z a b = 0 := by simp [pmat, hab]
    rw [h0]; simp
  · have hs : (if ε a then (1:ℂ) else -1) * (if ε b then 1 else -1) = -1 := by
      cases ha : ε a <;> cases hb : ε b <;> simp_all
    calc (if ε a then (1:ℂ) else -1) * pmat z a b * (if ε b then 1 else -1)
        = ((if ε a then (1:ℂ) else -1) * (if ε b then 1 else -1)) * pmat z a b := by ring
      _ = -pmat z a b := by rw [hs]; ring

theorem polarInv_toMK_inv {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have hu : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := k.2.1
  exact Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.mp hu)

private theorem pmat_conjTranspose_eq_self {ε : Fin n → Bool} (z : PCoord ε → ℂ) : (pmat z)ᴴ = pmat z := by
  ext a b
  simp only [Matrix.conjTranspose_apply, pmat]
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => lt_asymm h1.1 h.1
    simp only [dif_neg h2, dif_pos h1, star_star]
  · by_cases h3 : a < b ∧ ε b ≠ ε a
    · simp only [dif_neg h1, dif_pos h3]
    · simp only [dif_neg h1, dif_neg h3, star_zero]

private theorem Jm_mul_Jm_eq_oneFormalDegree (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem conjTranspose_Jm_eq_Jm (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem polarInv_key {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    Jm ε * (polarM (k, z))ᴴ * Jm ε = polarM (k⁻¹, adK k (-z)) := by
  have hK : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := k.2.1
  have hKJ : toMK k * Jm ε = Jm ε * toMK k := k.2.2
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_Jm_eq_oneFormalDegree ε
  have hJh : (Jm ε)ᴴ = Jm ε := conjTranspose_Jm_eq_Jm ε
  have hKKh : toMK k * (toMK k)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hK
  have hKhK : (toMK k)ᴴ * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.mp hK
  have hKhJ : (toMK k)ᴴ * Jm ε = Jm ε * (toMK k)ᴴ := by
    have h := congrArg Matrix.conjTranspose hKJ
    simp only [Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hKu : IsUnit (toMK k) := ⟨⟨toMK k, (toMK k)ᴴ, hKKh, hKhK⟩, rfl⟩
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hKinv : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_right_inv hKKh
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv hJJ
  have hE : (NormedSpace.exp (pmat z))ᴴ = NormedSpace.exp (pmat z) := by
    rw [← Matrix.exp_conjTranspose, pmat_conjTranspose_eq_self]
  have h1 : NormedSpace.exp (Jm ε * pmat z * (Jm ε)⁻¹) =
      Jm ε * NormedSpace.exp (pmat z) * (Jm ε)⁻¹ := Matrix.exp_conj _ _ hJu
  have h2 : NormedSpace.exp (toMK k * pmat (-z) * (toMK k)⁻¹) =
      toMK k * NormedSpace.exp (pmat (-z)) * (toMK k)⁻¹ := Matrix.exp_conj _ _ hKu
  rw [hJinv, polarInv_Jm_pmat] at h1
  rw [hKinv] at h2
  rw [show polarM (k, z) = toMK k * NormedSpace.exp (pmat z) from rfl,
    show polarM (k⁻¹, adK k (-z)) = toMK k⁻¹ * NormedSpace.exp (pmat (adK k (-z))) from rfl,
    polarInv_toMK_inv, pmat_adK, h2, Matrix.conjTranspose_mul, hE, polarInv_pmat_neg, h1]
  calc Jm ε * (NormedSpace.exp (pmat z) * (toMK k)ᴴ) * Jm ε
      = Jm ε * NormedSpace.exp (pmat z) * ((toMK k)ᴴ * Jm ε) := by simp only [Matrix.mul_assoc]
    _ = Jm ε * NormedSpace.exp (pmat z) * (Jm ε * (toMK k)ᴴ) := by rw [hKhJ]
    _ = ((toMK k)ᴴ * toMK k) * (Jm ε * NormedSpace.exp (pmat z) * Jm ε) * (toMK k)ᴴ := by
        rw [hKhK, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    _ = (toMK k)ᴴ * (toMK k * (Jm ε * NormedSpace.exp (pmat z) * Jm ε) * (toMK k)ᴴ) := by
        simp only [Matrix.mul_assoc]

theorem polarInv_apply (ε : Fin n → Bool) (S : Set (UJ ε)) (hS : MeasurableSet S) :
    muPolar ε S = ∫⁻ k, ∫⁻ z, (intMuCD_eM ε '' S).indicator (1 : (Fin n → Fin n → ℂ) → ENNReal)
      (intMuCD_pM ε (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hce : Topology.IsClosedEmbedding (intMuCD_eM ε) := isClosedEmbedding_toM ε
  have he : MeasurableEmbedding (intMuCD_eM ε) := hce.measurableEmbedding
  have hT : MeasurableSet (intMuCD_eM ε '' S) := he.measurableSet_image.2 hS
  have hF : Measurable ((intMuCD_eM ε '' S).indicator (1 : (Fin n → Fin n → ℂ) → ENNReal)) :=
    measurable_one.indicator hT
  have h := lintegral_muPolar ε _ hF
  rw [← lintegral_indicator_one hS]
  refine Eq.trans ?_ h
  refine lintegral_congr (fun g => ?_)
  change S.indicator 1 g = (intMuCD_eM ε '' S).indicator 1 (intMuCD_eM ε g)
  classical
  simp only [Set.indicator_apply, he.injective.mem_set_image, Pi.one_apply]

theorem muPolar_inv (ε : Fin n → Bool) : Measure.map (fun x : UJ ε => x⁻¹) (muPolar ε) = muPolar ε := by
  have hinv : Measurable (fun x : UJ ε => x⁻¹) := continuous_inv.measurable
  have hinvK : Measurable (fun x : KG ε => x⁻¹) := continuous_inv.measurable
  have hce : Topology.IsClosedEmbedding (intMuCD_eM ε) := isClosedEmbedding_toM ε
  have he : MeasurableEmbedding (intMuCD_eM ε) := hce.measurableEmbedding
  ext S hS
  rw [Measure.map_apply hinv hS, polarInv_apply ε _ (hinv hS), polarInv_apply ε S hS]
  have hT : MeasurableSet (intMuCD_eM ε '' S) := he.measurableSet_image.2 hS
  have hpt : ∀ (k : KG ε) (z : PCoord ε → ℂ),
      (intMuCD_eM ε '' ((fun x : UJ ε => x⁻¹) ⁻¹' S)).indicator
          (1 : (Fin n → Fin n → ℂ) → ENNReal) (intMuCD_pM ε (k, z)) =
        (intMuCD_eM ε '' S).indicator 1 (intMuCD_pM ε (k⁻¹, adK k (-z))) := by
    intro k z
    obtain ⟨g, hg⟩ : polarM (k, z) ∈ Set.range (fun g : UJ ε => toM g) := by
      rw [range_toM]; exact polarM_inUJ (k, z)
    have hg' : toM g = polarM (k, z) := hg
    have e1 : intMuCD_pM ε (k, z) = intMuCD_eM ε g := hg'.symm
    have e2 : intMuCD_pM ε (k⁻¹, adK k (-z)) = intMuCD_eM ε g⁻¹ := by
      show polarM _ = toM g⁻¹
      rw [toM_inv, hg', polarInv_key]
    rw [e1, e2]
    classical
    simp only [Set.indicator_apply, he.injective.mem_set_image, Set.mem_preimage, Pi.one_apply]
  let G : KG ε × (PCoord ε → ℂ) → ENNReal := fun kz =>
    (intMuCD_eM ε '' S).indicator 1 (intMuCD_pM ε kz) * ENNReal.ofReal (Jac kz.2)
  have hG : Measurable G :=
    ((measurable_one.indicator hT).comp (intMuCD_measurable_pM ε)).mul
      (ENNReal.measurable_ofReal.comp ((jac_continuous ε).measurable.comp measurable_snd))
  have hH : Measurable fun k => ∫⁻ w, G (k, w) := hG.lintegral_prod_right'
  have step : ∀ k : KG ε, ∫⁻ z, (intMuCD_eM ε '' ((fun x : UJ ε => x⁻¹) ⁻¹' S)).indicator 1
      (intMuCD_pM ε (k, z)) * ENNReal.ofReal (Jac z) = ∫⁻ w, G (k⁻¹, w) := by
    intro k
    have hφ : MeasurePreserving (fun z : PCoord ε → ℂ => adK k (-z)) volume volume :=
      (adK_measurePreserving k).comp (Measure.measurePreserving_neg volume)
    have hm : Measurable (fun w => G (k⁻¹, w)) := hG.comp measurable_prodMk_left
    refine Eq.trans ?_ (hφ.lintegral_comp hm)
    refine lintegral_congr fun z => ?_
    show _ = G (k⁻¹, adK k (-z))
    simp only [G, hpt, jac_adK, jac_neg]
  calc ∫⁻ k, ∫⁻ z, (intMuCD_eM ε '' ((fun x : UJ ε => x⁻¹) ⁻¹' S)).indicator 1
        (intMuCD_pM ε (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε)
      = ∫⁻ k, (fun k => ∫⁻ w, G (k, w)) ((fun x : KG ε => x⁻¹) k) ∂(dk ε) := lintegral_congr step
    _ = ∫⁻ k, (∫⁻ w, G (k, w)) ∂(Measure.map (fun x : KG ε => x⁻¹) (dk ε)) := by
        rw [lintegral_map hH hinvK]
    _ = _ := by rw [(dk_props ε).2.2.2]

end ReciprocityTheory.ChartRestriction.DS
