import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH lc_G sc_G lc_GLf sc_GLf t2_GL_finite_adeles borelSpaceH

namespace PositivityTheory.Rg.BcB.F.Rd.B

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem sc_H : SecondCountableTopology (H E a b) :=
  (splitH (E := E) a b).toHomeomorph.symm.secondCountableTopology

theorem lc_H : LocallyCompactSpace (H E a b) :=
  (splitH (E := E) a b).toHomeomorph.symm.isClosedEmbedding.locallyCompactSpace

theorem t2_block_group : T2Space (H E a b) :=
  (splitH (E := E) a b).toHomeomorph.t2Space

attribute [local instance] sc_H lc_H t2_block_group

theorem integrable_conv2 (μ : Measure (H E a b)) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    (φ₁ φ₂ g : H E a b → ℂ) (h₁ : IsTestH φ₁) (h₂ : IsTestH φ₂) (hg : Continuous g) :
    Integrable (fun p : H E a b × H E a b => φ₁ p.1 * φ₂ (p.1⁻¹ * p.2) * g p.2) (μ.prod μ) := by
  have hc : Continuous (fun p : H E a b × H E a b => φ₁ p.1 * φ₂ (p.1⁻¹ * p.2) * g p.2) :=
    ((h₁.1.comp continuous_fst).mul (h₂.1.comp (continuous_fst.inv.mul continuous_snd))).mul (hg.comp continuous_snd)
  refine hc.integrable_of_hasCompactSupport ?_
  have hK : IsCompact ((fun q : H E a b × H E a b => (q.1, q.1 * q.2)) '' (tsupport φ₁ ×ˢ tsupport φ₂)) :=
    (h₁.2.isCompact.prod h₂.2.isCompact).image (continuous_fst.prodMk (continuous_fst.mul continuous_snd))
  haveI ht : T2Space (H E a b) := t2_block_group
  haveI : T2Space (H E a b × H E a b) := Prod.t2Space
  refine HasCompactSupport.intro' hK hK.isClosed fun p hp => ?_
  by_contra hne
  apply hp
  refine ⟨(p.1, p.1⁻¹ * p.2), ⟨?_, ?_⟩, by simp⟩
  · exact subset_tsupport _ fun h => hne (by simp [h])
  · exact subset_tsupport _ fun h => hne (by simp [h])

theorem convolution_pairing_test_entry (μ : Measure (H E a b)) [IsFiniteMeasureOnCompacts μ] [SFinite μ] [μ.IsMulLeftInvariant]
    (φ₁ φ₂ g : H E a b → ℂ) (h₁ : IsTestH φ₁) (h₂ : IsTestH φ₂) (hg : Continuous g) :
    ∫ y, (∫ z, φ₁ z * φ₂ (z⁻¹ * y) ∂μ) * g y ∂μ = ∫ z, φ₁ z * ∫ w, φ₂ w * g (z * w) ∂μ ∂μ := by
  have hI := integrable_conv2 μ φ₁ φ₂ g h₁ h₂ hg
  have e1 : ∀ y, (∫ z, φ₁ z * φ₂ (z⁻¹ * y) ∂μ) * g y = ∫ z, φ₁ z * φ₂ (z⁻¹ * y) * g y ∂μ := fun y =>
    (integral_mul_const (g y) _).symm
  simp_rw [e1]
  rw [← integral_integral_swap (f := fun z y => φ₁ z * φ₂ (z⁻¹ * y) * g y) hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [← integral_mul_left_eq_self (μ := μ) (fun y => φ₁ z * φ₂ (z⁻¹ * y) * g y) z, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [inv_mul_cancel_left]
  ring

theorem conv_mulM (D : Dom E a b) {ι : Type} [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E a b → ℂ)) (h₁ : IsTestM Φ₁)
    (h₂ : IsTestM Φ₂) (f : ι → H E a b → ℂ) (hf : ∀ i, Continuous (f i)) :
    PositivityTheory.Rg.BcB.E.conv D.μ (mulM D.μ Φ₁ Φ₂) f = PositivityTheory.Rg.BcB.E.conv D.μ Φ₁ (PositivityTheory.Rg.BcB.E.conv D.μ Φ₂ f) := by
  have := haar_of_dom D
  funext i x
  have hg : ∀ j, Continuous fun y => f j (x * y) := fun j => (hf j).comp (continuous_const.mul continuous_id)
  have hI : ∀ j k, Integrable (fun p : H E a b × H E a b => Φ₁ i k p.1 * Φ₂ k j (p.1⁻¹ * p.2) * f j (x * p.2))
      (D.μ.prod D.μ) := fun j k => integrable_conv2 D.μ _ _ _ (h₁ i k) (h₂ k j) (hg j)

  have hL : ∀ j, ∫ y, (∑ k, ∫ z, Φ₁ i k z * Φ₂ k j (z⁻¹ * y) ∂D.μ) * f j (x * y) ∂D.μ =
      ∑ k, ∫ y, (∫ z, Φ₁ i k z * Φ₂ k j (z⁻¹ * y) ∂D.μ) * f j (x * y) ∂D.μ := by
    intro j
    simp_rw [Finset.sum_mul]
    refine integral_finsetSum _ fun k _ => ?_
    have := (hI j k).integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    exact integral_mul_const (f j (x * y)) _

  have hR : ∀ k, ∫ z, Φ₁ i k z * (∑ j, ∫ w, Φ₂ k j w * f j (x * z * w) ∂D.μ) ∂D.μ =
      ∑ j, ∫ z, Φ₁ i k z * ∫ w, Φ₂ k j w * f j (x * z * w) ∂D.μ ∂D.μ := by
    intro k
    simp_rw [Finset.mul_sum]
    refine integral_finsetSum _ fun j _ => ?_
    have := (hI j k).integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [← integral_mul_left_eq_self (μ := D.μ) (fun y => Φ₁ i k z * Φ₂ k j (z⁻¹ * y) * f j (x * y)) z,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [inv_mul_cancel_left, mul_assoc]
  show ∑ j, ∫ y, (∑ k, ∫ z, Φ₁ i k z * Φ₂ k j (z⁻¹ * y) ∂D.μ) * f j (x * y) ∂D.μ =
    ∑ k, ∫ z, Φ₁ i k z * (∑ j, ∫ w, Φ₂ k j w * f j (x * z * w) ∂D.μ) ∂D.μ
  simp_rw [hL, hR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  have := convolution_pairing_test_entry D.μ (Φ₁ i k) (Φ₂ k j) (fun y => f j (x * y)) (h₁ i k) (h₂ k j) (hg j)
  simpa only [mul_assoc] using this

end PositivityTheory.Rg.BcB.F.Rd.B

end
