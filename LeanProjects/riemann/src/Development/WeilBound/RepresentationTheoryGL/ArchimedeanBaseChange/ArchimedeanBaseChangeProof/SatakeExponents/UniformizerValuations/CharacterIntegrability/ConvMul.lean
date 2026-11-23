import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ActHecke
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)

namespace PositivityTheory.Rg.BcB.F.R3

section Gen

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] [T2Space K]

theorem integrable_convolution_pairing (μ : Measure K) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    (φ₁ φ₂ g : K → ℂ) (h₁ : Continuous φ₁ ∧ HasCompactSupport φ₁) (h₂ : Continuous φ₂ ∧ HasCompactSupport φ₂)
    (hg : Continuous g) :
    Integrable (fun p : K × K => φ₁ p.1 * φ₂ (p.1⁻¹ * p.2) * g p.2) (μ.prod μ) := by
  have hc : Continuous (fun p : K × K => φ₁ p.1 * φ₂ (p.1⁻¹ * p.2) * g p.2) :=
    ((h₁.1.comp continuous_fst).mul (h₂.1.comp (continuous_fst.inv.mul continuous_snd))).mul (hg.comp continuous_snd)
  refine hc.integrable_of_hasCompactSupport ?_
  have hK : IsCompact ((fun q : K × K => (q.1, q.1 * q.2)) '' (tsupport φ₁ ×ˢ tsupport φ₂)) :=
    (h₁.2.isCompact.prod h₂.2.isCompact).image (continuous_fst.prodMk (continuous_fst.mul continuous_snd))
  refine HasCompactSupport.intro' hK hK.isClosed fun p hp => ?_
  by_contra hne
  apply hp
  refine ⟨(p.1, p.1⁻¹ * p.2), ⟨?_, ?_⟩, by simp⟩
  · exact subset_tsupport _ fun h => hne (by simp [h])
  · exact subset_tsupport _ fun h => hne (by simp [h])

theorem convolution_pairing_fubini (μ : Measure K) [IsFiniteMeasureOnCompacts μ] [SFinite μ] [μ.IsMulLeftInvariant]
    (φ₁ φ₂ g : K → ℂ) (h₁ : Continuous φ₁ ∧ HasCompactSupport φ₁) (h₂ : Continuous φ₂ ∧ HasCompactSupport φ₂)
    (hg : Continuous g) :
    ∫ y, (∫ z, φ₁ z * φ₂ (z⁻¹ * y) ∂μ) * g y ∂μ = ∫ z, φ₁ z * ∫ w, φ₂ w * g (z * w) ∂μ ∂μ := by
  have hI := integrable_convolution_pairing μ φ₁ φ₂ g h₁ h₂ hg
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

end Gen

attribute [local instance] borelG borelF borelH lc_GLf sc_GLf t2_GL_finite_adeles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem borelSpaceHf : BorelSpace (Hf E a b) := ⟨rfl⟩

attribute [local instance] borelSpaceHf

theorem finH_mul (g h : Hf E a b) : finH (g * h) = finH g * finH h := by
  simp [finH, map_mul]

theorem convF_mulF_eq_convF_convF {A κ : Type} [Fintype κ] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
    (ψ ψ' : Matrix κ κ (Hf E a b → ℂ)) (hψ : IsFinM ψ) (hψ' : IsFinM ψ') (F : A × κ → H E a b → ℂ)
    (hF : ∀ i x, Continuous fun h => F i (x * finH h)) :
    convF ν (mulF ν ψ ψ') F = convF ν ψ (convF ν ψ' F) := by
  funext i x
  have hg : ∀ j, Continuous fun y => F (i.1, j) (x * finH y) := fun j => hF _ x
  have hI : ∀ j k, Integrable (fun p : Hf E a b × Hf E a b =>
      ψ i.2 k p.1 * ψ' k j (p.1⁻¹ * p.2) * F (i.1, j) (x * finH p.2)) (ν.prod ν) :=
    fun j k => integrable_convolution_pairing ν _ _ _ (hψ i.2 k) (hψ' k j) (hg j)
  have hL : ∀ j, ∫ y, (∑ k, ∫ z, ψ i.2 k z * ψ' k j (z⁻¹ * y) ∂ν) * F (i.1, j) (x * finH y) ∂ν =
      ∑ k, ∫ y, (∫ z, ψ i.2 k z * ψ' k j (z⁻¹ * y) ∂ν) * F (i.1, j) (x * finH y) ∂ν := by
    intro j
    simp_rw [Finset.sum_mul]
    refine integral_finsetSum _ fun k _ => ?_
    have := (hI j k).integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    exact integral_mul_const (F (i.1, j) (x * finH y)) _
  have hR : ∀ k, ∫ z, ψ i.2 k z * (∑ j, ∫ w, ψ' k j w * F (i.1, j) (x * finH z * finH w) ∂ν) ∂ν =
      ∑ j, ∫ z, ψ i.2 k z * ∫ w, ψ' k j w * F (i.1, j) (x * finH z * finH w) ∂ν ∂ν := by
    intro k
    simp_rw [Finset.mul_sum]
    refine integral_finsetSum _ fun j _ => ?_
    have := (hI j k).integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [← integral_mul_left_eq_self (μ := ν)
      (fun y => ψ i.2 k z * ψ' k j (z⁻¹ * y) * F (i.1, j) (x * finH y)) z, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [inv_mul_cancel_left, finH_mul, mul_assoc]
  show ∑ j, ∫ y, (∑ k, ∫ z, ψ i.2 k z * ψ' k j (z⁻¹ * y) ∂ν) * F (i.1, j) (x * finH y) ∂ν =
    ∑ k, ∫ z, ψ i.2 k z * (∑ j, ∫ w, ψ' k j w * F (i.1, j) (x * finH z * finH w) ∂ν) ∂ν
  simp_rw [hL, hR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  have := convolution_pairing_fubini ν (ψ i.2 k) (ψ' k j) (fun y => F (i.1, j) (x * finH y)) (hψ i.2 k) (hψ' k j) (hg j)
  simpa only [finH_mul, mul_assoc] using this

end PositivityTheory.Rg.BcB.F.R3

end
