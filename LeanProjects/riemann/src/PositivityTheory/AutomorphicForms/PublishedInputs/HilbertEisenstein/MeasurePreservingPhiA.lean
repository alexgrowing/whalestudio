import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix ENNReal
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published Filter

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace L6

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem omega_diagonal (ω : HChar F) (a : Fˣ) : ω.1 (diagonal F a) = 1 := ω.2.2 a

theorem module_tau_diag (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) (a : Fˣ) :
    (ideleModule F (tau t u * diagonal F a) : ℝ) = t := by
  have hu : ideleModule F (u : IdeleGroup F) = 1 := u.2
  rw [tau, map_mul, map_mul, ideleModule_diagonal, ideleModule_moduleSection, hu, mul_one, mul_one]

theorem G_unfold (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (ξ : F) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) (a : Fˣ) :
    kern c Y (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) ξ *
      ((ω.1 (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℂˣ) : ℂ)⁻¹ *
      ((ideleModule F (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℝ) : ℂ) =
    kern c Y (tau t u * diagonal F a) ξ * wt ω t u := by
  have he : diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F) = tau t u * diagonal F a := by
    rw [tau, mul_assoc, mul_comm]
  rw [he, module_tau_diag, map_mul, omega_diagonal, mul_one, wt, mul_assoc]

theorem tsum_G (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (ξ : F) (t : {r : ℝ // 0 < r})
    (u : normOneSubgroup F) :
    ∑' a : Fˣ, kern c Y (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) ξ *
      ((ω.1 (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℂˣ) : ℂ)⁻¹ *
      ((ideleModule F (diagonal F a * moduleSection (w0 F) t * (u : IdeleGroup F)) : ℝ) : ℂ) =
    coefK c Y (tau t u) ξ * wt ω t u := by
  simp_rw [G_unfold]
  rw [coefK, tsum_mul_right]

def phiA (a : Fˣ) (p : {r : ℝ // 0 < r} × normOneSubgroup F) : IdeleGroup F :=
  diagonal F a * moduleSection (w0 F) p.1 * (p.2 : IdeleGroup F)

theorem continuous_phiA (a : Fˣ) : Continuous (phiA (F := F) a) :=
  (continuous_const.mul ((continuous_moduleSection (w0 F)).comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)

theorem measurePreserving_phiA (a : Fˣ) :
    MeasurePreserving (phiA (F := F) a) (posRealMeasure.prod (normOneMeasure F)) (ideleMeasure F) := by
  have h0 : MeasurePreserving (normOneSplitting (w0 F)).toHomeomorph.toMeasurableEquiv (ideleMeasure F)
      ((normOneMeasure F).prod posRealMeasure) := measurePreserving_normOneSplitting (w0 F)
  have h1 := (MeasurePreserving.symm _ h0).comp (Measure.measurePreserving_swap
    (μ := posRealMeasure) (ν := normOneMeasure F))
  have h3 := (measurePreserving_mul_left (ideleMeasure F) (diagonal F a)).comp h1
  convert h3 using 1
  funext p
  change diagonal F a * moduleSection (w0 F) p.1 * (p.2 : IdeleGroup F) =
    diagonal F a * ((p.2 : IdeleGroup F) * moduleSection (w0 F) p.1)
  rw [mul_assoc, mul_comm (moduleSection (w0 F) p.1)]

theorem muE_ac : muE F ≪ posRealMeasure.prod (normOneMeasure F) := by
  have h : muE F = (posRealMeasure.prod (normOneMeasure F)).restrict (Set.univ ×ˢ normOneFundamentalDomain F) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [h]
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

theorem lintegral_unfold {g : IdeleGroup F → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, ∑' a : Fˣ, g (phiA a p) ∂(muE F) = ∫⁻ x, g x ∂ideleMeasure F := by
  have hm : ∀ a : Fˣ, Measurable fun p => g (phiA a p) := fun a => hg.comp (continuous_phiA a).measurable
  have hin : ∀ t : {r : ℝ // 0 < r}, ∫⁻ u in normOneFundamentalDomain F, ∑' a : Fˣ, g (phiA a (t, u)) ∂normOneMeasure F
      = ∫⁻ u, g (phiA 1 (t, u)) ∂normOneMeasure F := by
    intro t
    have h𝓕 := isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)
    let e : Fˣ ≃ (diagonalNormOne F).op := (diagonalNormOneEquiv F).trans (diagonalNormOne F).equivOp
    rw [lintegral_tsum (f := fun a u => g (phiA a (t, u))) (fun a => ((hm a).comp measurable_prodMk_left).aemeasurable),
      h𝓕.lintegral_eq_tsum'',
      ← e.tsum_eq]
    refine tsum_congr fun a => lintegral_congr fun u => ?_
    change g (phiA a (t, u)) = g (phiA 1 (t, u * diagonalToNormOne F a))
    simp only [phiA, map_one, one_mul, Subgroup.coe_mul, coe_diagonalToNormOne]
    congr 1
    ac_rfl
  rw [lintegral_prod _ (Measurable.tsum hm).aemeasurable]
  simp_rw [hin]
  rw [← (measurePreserving_phiA 1).lintegral_comp hg, lintegral_prod _ (hm 1).aemeasurable]

theorem integrable_unfold {G : IdeleGroup F → ℂ} (hG : Integrable G (ideleMeasure F)) :
    Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ∑' a : Fˣ, G (phiA a p)) (muE F) := by
  set G' := hG.1.mk G
  have hG'm : StronglyMeasurable G' := hG.1.stronglyMeasurable_mk
  have hGG' : G =ᵐ[ideleMeasure F] G' := hG.1.ae_eq_mk
  have hae : ∀ᵐ p ∂(muE F), ∀ a : Fˣ, G (phiA a p) = G' (phiA a p) := by
    refine ae_all_iff.2 fun a => muE_ac.ae_le ?_
    exact (measurePreserving_phiA a).quasiMeasurePreserving.ae_eq_comp hGG'
  have hP' : Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ∑' a : Fˣ, G' (phiA a p)) (muE F) := by
    refine ⟨(Measurable.tsum fun a => hG'm.measurable.comp (continuous_phiA a).measurable).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ p, ‖∑' a : Fˣ, G' (phiA a p)‖ₑ ∂(muE F)
        ≤ ∫⁻ p, ∑' a : Fˣ, ‖G' (phiA a p)‖ₑ ∂(muE F) := lintegral_mono fun p => enorm_tsum_le_tsum_enorm
      _ = ∫⁻ x, ‖G' x‖ₑ ∂ideleMeasure F := lintegral_unfold hG'm.measurable.enorm
      _ = ∫⁻ x, ‖G x‖ₑ ∂ideleMeasure F := lintegral_congr_ae (hGG'.fun_comp _).symm
      _ < ∞ := hG.2
  refine hP'.congr ?_
  filter_upwards [hae] with p hp
  exact tsum_congr fun a => (hp a).symm

end L6

open L6 in
theorem sUnfold_statement : SUnfold := by
  intro F _ _ _ ω c H Y ξ hG
  set G : IdeleGroup F → ℂ := fun τ => kern c Y τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ)
  have hP : ∀ p : {r : ℝ // 0 < r} × normOneSubgroup F,
      coefK c Y (tau p.1 p.2) ξ * wt ω p.1 p.2 = ∑' a : Fˣ, G (phiA a p) := fun p => (tsum_G ω c Y ξ p.1 p.2).symm
  simp_rw [hP]
  rw [integral_prod _ (integrable_unfold hG), integral_ideleMeasure_eq_integral_fundamentalDomain (w0 F) hG]
  rfl

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
