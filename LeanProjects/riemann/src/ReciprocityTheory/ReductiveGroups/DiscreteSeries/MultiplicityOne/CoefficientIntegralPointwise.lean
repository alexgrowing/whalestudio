import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HsInnerSmulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HilbertSchmidtContinuousFunctional

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 HilbertSchmidtFunctionals

theorem coefficient_integral_pointwise (h : UnitaryGroupStructuralFacts) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D)
    (hCW : IsClosedSubgroup (UWset k r D.z)) (d : ℝ) (hd : IsFdegG D X d) (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs)
    (X₀ : Wp →L[ℂ] Wp) (hf : ∀ g ∈ GV k r, f g = mc X x y g) (p : SS k r) (hp : D.inSS p) :
    xiTau D (1, 1) p * Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) p =
      hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (beInt D X y b₂ p.1)).comp (beInt D X x a₂ p.2)) / (d : ℂ) := by
  rw [stCut1 h k r Wp D X hD d hd f x y a₂ b₂ X₀ hf p hp, character_at_one_eq_product D hD.z_eq, hilbertSchmidt_functional_apply]
  simp only [beInt, map_smulₛₗ, adjoint_representation_inv D hCW hp.1, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, hilbertSchmidt_inner_smul_left, starRingEnd_apply, star_mul', star_star]
  ring

theorem stCut2 (h : UnitaryGroupStructuralFacts) : StCut2 := by
  intro k r Wp _ _ _ D X hD d hd f x y a₂ b₂ X₀ hf hU hV
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have h' := h
  obtain ⟨hB2, -⟩ := h'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCW, -⟩ := hB2
  have := sigmaFinite_of_haar_on D.haarW; have := sigmaFinite_of_haar_on D.haarN
  have hμ : D.μSS = (D.μW.prod D.μN).prod (D.μW.prod D.μN) := by
    show (D.μW.prod D.μN).prod (D.μW'.prod D.μN) = _
    rw [hD.μW_eq]
  have hΦi : Integrable (fun q : SS k r => hilbertSchmidtContinuousFunctional X₀
      ((ContinuousLinearMap.adjoint (beInt D X y b₂ q.1)).comp (beInt D X x a₂ q.2))) D.μSS := by
    rw [hμ]; exact integrable_hilbertSchmidt_pairing X₀ hV hU
  have hpt : ∀ᵐ p ∂D.μSS, xiTau D (1, 1) p * Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) p =
      hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (beInt D X y b₂ p.1)).comp (beInt D X x a₂ p.2)) / (d : ℂ) :=
    (ae_mem_big_cell D).mono fun p hp => coefficient_integral_pointwise h D X hD (hCW k r D.z) d hd f x y a₂ b₂ X₀ hf p hp
  refine ⟨?_, ?_⟩
  · have hg : Integrable (fun p => star (xiTau D (1, 1) p) * (hilbertSchmidtContinuousFunctional X₀
        ((ContinuousLinearMap.adjoint (beInt D X y b₂ p.1)).comp (beInt D X x a₂ p.2)) / (d : ℂ))) D.μSS :=
      (hΦi.div_const (d : ℂ)).norm.mono'
        ((character_continuous D (1, 1)).star.aestronglyMeasurable.mul (hΦi.div_const _).aestronglyMeasurable)
        (ae_of_all _ fun p => by rw [norm_mul, norm_star, norm_character_eq_one, one_mul])
    refine hg.congr (hpt.mono fun p hp => ?_)
    dsimp only
    rw [← hp, ← mul_assoc, star_character_mul_self, one_mul]
  · rw [integral_congr_ae hpt, integral_div, hμ, integral_hilbertSchmidt_pairing X₀ hV hU, hilbertSchmidt_functional_apply]
    rfl

end ReciprocityTheory.ChartRestriction.DS.Mult1
