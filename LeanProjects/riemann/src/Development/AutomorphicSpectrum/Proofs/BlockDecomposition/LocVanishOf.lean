import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilradicalChangeOfVariablesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientVanishingStatement

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

theorem locVanish_of (hN : NilChange) (hQ : QuotVanish) : LocVanish := by
  intro n _ _ μ _ f u d μd _ W₁ W₂ hf hfc hV hsep hW1 hle h12 h21 hu hub huK huT huN
  have hTw : Continuous fun x : GL (Fin n) ℂ => twConj (thC n) x d :=
    (continuous_inv.mul continuous_const).mul continuous_thC
  refine hQ n μ d μd W₁ W₂ hsep hW1 hle h12 h21 _
    (((hf.comp hTw).measurable).mul hu) (fun t ht x => ?_) (fun x k hk => ?_) ?_
  · show f (twConj (thC n) (t * x) d) * u (t * x) = f (twConj (thC n) x d) * u x
    rw [twConj_mul_left _ _ ht, huT t ht]
  · show f (twConj (thC n) (x * k) d) * u (x * k) = f (twConj (thC n) x d) * u x
    have : twConj (thC n) (x * k) d = twConj (thC n) k (twConj (thC n) x d) := by
      simp only [twConj, map_mul, _root_.mul_inv_rev, mul_assoc]
    rw [this, hV.1 k _ hk, huK x k hk]
  · intro _ _ ν _ q
    obtain ⟨Φ, hΦc, hΦ, hΦν⟩ := hN n d W₁ W₂ hsep hW1 hle h12 h21
    obtain ⟨c, hc⟩ := hΦν ν

    set g : nilrad W₁ W₂ → ℂ := fun Y => f (q⁻¹ * uOf Y * d * thC n q) with hg
    have hgc : Continuous g :=
      hf.comp (((continuous_const.mul continuous_uOf).mul continuous_const).mul continuous_const)
    have e1 : ∀ X : nilrad W₁ W₂,
        f (twConj (thC n) (uOf X * q) d) * u (uOf X * q) = u q * g (Φ X) := fun X => by
      have hm : (uOf X).val - 1 ∈ nilrad W₁ W₂ := by simpa using X.2
      rw [huN _ hm, mul_comm]
      congr 2
      simp only [hg, hΦ, twConj, map_mul, _root_.mul_inv_rev]
      group
    have e2 : ∫ X, g (Φ X) ∂ν = (c : ℝ) • ∫ Y, g Y ∂ν := by
      rw [← integral_map hΦc.measurable.aemeasurable hgc.aestronglyMeasurable, hc,
        integral_smul_measure]
      simp
    simp only [e1]
    rw [integral_const_mul, e2]
    suffices h : ∫ Y, g Y ∂ν = 0 by simp [h]

    letI : MeasurableSpace (nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) := borel _
    haveI : BorelSpace (nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) := ⟨rfl⟩
    have hcn := continuous_conjNil q W₁ W₂
    haveI : (ν.map (conjNil q W₁ W₂)).IsAddHaarMeasure :=
      (conjNil q W₁ W₂).isAddHaarMeasure_map ν hcn (continuous_conjNil_symm q W₁ W₂)
    have key := hV.2 (twConj (thC n) q d) (img q⁻¹ W₁) (img q⁻¹ W₂) (img_ne_bot _ hW1)
      (img_le_img _ hle) (by rw [perpD_twConj, h12]) (by rw [perpD_twConj, h21]) uOf
      (fun X => uOf_val X) (ν.map (conjNil q W₁ W₂))
    have hcont : Continuous fun Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) =>
        f (uOf Z * twConj (thC n) q d) := hf.comp (continuous_uOf.mul continuous_const)
    rw [integral_map hcn.measurable.aemeasurable hcont.aestronglyMeasurable] at key
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    show f _ = f _
    rw [uOf_conjNil]
    congr 1
    simp only [twConj]
    group

theorem locVanish : LocVanish := locVanish_of GlobalTheory.T.nilradical_change_of_variables GlobalTheory.T.quotient_vanishing

end GlobalTheory.CompanionTheory.LocVan
end
