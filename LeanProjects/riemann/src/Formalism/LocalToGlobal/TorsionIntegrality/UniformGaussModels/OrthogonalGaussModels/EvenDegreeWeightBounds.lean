import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussEveryInt7
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussEveryOrth7
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency
import Formalism.GaussJetBounds.OneLetterGaussJets.GainDominatesOddLevelSum

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (cm2 cm3 cm4)

theorem matrix_entries_all_disc_seven : ThmAEntryAll7 := by
  intro l _ _ g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN d N0 N1 _ hd2 hde hN0 ιr _ _ om oms hO hT hζ U0 Φ hU0
    hΦ0 hΦ TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 hJ δ hδ
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨K1, ζ, be, g, U, hK1, hζ', hbe, hg0, hg, hUi, heq⟩ := CohomologyFunctoriality₂.thetaForm l (CM.MaximalUnramifiedExtension l) σ hσ
    (CM.MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2 d N0 N1 hd2 hde ιr om oms hO hT hζ U0 Φ hU0 hΦ0 hΦ
  rw [heq]
  exact Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAEntry7 l d N0 N1 hσ.2.1 hd2 hde hN0 K1 hK1 ζ hζ' be hbe g hg0 hg U hUi (-1)
    (Or.inr rfl) TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 hJ δ hδ

theorem gauss_form_all_disc_seven : ThmAGaussAll7 := by
  intro l _ _ g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN d N0 N1 _ hd2 hde hN0 ιr _ _ om oms hO hT hζ U0 Φ hU0
    hΦ0 hΦ TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 hJ n
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨K1, ζ, be, g, U, hK1, hζ', hbe, hg0, hg, hUi, heq⟩ := CohomologyFunctoriality₂.thetaForm l (CM.MaximalUnramifiedExtension l) σ hσ
    (CM.MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2 d N0 N1 hd2 hde ιr om oms hO hT hζ U0 Φ hU0 hΦ0 hΦ
  rw [heq]
  exact Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAGauss7 l d N0 N1 hσ.2.1 hd2 hde hN0 K1 hK1 ζ hζ' be hbe g hg0 hg U hUi (-1)
    (Or.inr rfl) TT colN p hp hp1 I nu1 nu2 size h1 h2 h3 hJ n

theorem one_letter_gauss_all_disc_seven : OneLetterGaussAll7 := by
  intro l _ _ g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN N0 N1 C U0 Φ hU0 hΦ0 hΦ p hp I n
  obtain ⟨a1, a2, a3⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨ζ, hζ⟩ := FAux.exists_root2 l
  obtain ⟨U, hUi, hUeq⟩ := single_letter_theta_factorization (CM.MaximalUnramifiedExtension l) ℂ_[l] l N0 N1 σ (CM.MaximalUnramifiedExtension l).subtype hσ (FAux.norm_coe l) F hF _
    a1 a2 ζ hζ _ a3 U0 Φ hU0 hΦ0 hΦ
  obtain ⟨g, hg0, hg, -⟩ := Formalism.DworkPowerSeriesWeights.generalized_log_inverse.{0, 0} ℂ_[l] l hσ.1
    (Fin N0 × Fin N1) id
  have hg' : ∀ y, MvPowerSeries.subst g (Formalism.DworkPowerSeriesWeights.oneLog (K := ℂ_[l]) l y) = MvPowerSeries.X y := by
    intro y
    rw [(Formalism.DworkPowerSeriesWeights.logarithm_weight_comparison.{0} ℂ_[l] l 2 N0 N1).2.2 y]
    exact hg y
  obtain ⟨hT1, hT2, -, -⟩ := Formalism.DworkPowerSeriesWeights.admissibleTransfer (CM.MaximalUnramifiedExtension l) ℂ_[l] (CM.MaximalUnramifiedExtension l).subtype
    (FAux.norm_coe l) l 2 N0 N1 ⊤ ζ
    (beMean (d := 2) l σ _ (fun _ : Unit => (1 : CM.MaximalUnramifiedExtension l)) (fun _ => 1) ζ)
  rw [hUeq g hg0 hg']
  exact Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.oneLetterGauss7 l N0 N1 C hσ.2.1 _ (hT1 (unramified_top (CM.MaximalUnramifiedExtension l) l σ hσ))
    ((CM.MaximalUnramifiedExtension l).subtype ζ) (hζ.map_of_injective (CM.MaximalUnramifiedExtension l).subtype.injective) _
    (hT2 (biextension_hypotheses_of_level_one (CM.MaximalUnramifiedExtension l) l 2 σ hσ le_rfl (by decide) F hF _ a1 Unit _ _ (SingleLetterLog.owOK_two σ) ζ hζ))
    1 (by simp) g hg0 hg' U hUi (-1) (Or.inr rfl) p hp I n

theorem matrix_entries_every_integral_disc_seven : ThmAEntryEveryInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨s2, hs2, hc2, fun σ hσ F hF => matrix_entries_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem matrix_entries_integral_disc_seven : ThmAEntryInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, hs2, hc2, tail⟩ := matrix_entries_every_integral_disc_seven dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, hg, hε, hth, hs2, hc2, tail⟩

theorem gauss_form_every_integral_disc_seven : ThmAGaussEveryInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨s2, hs2, hc2, fun σ hσ F hF => gauss_form_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem gauss_form_integral_disc_seven : ThmAGaussInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, hs2, hc2, tail⟩ := gauss_form_every_integral_disc_seven dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, hg, hε, hth, hs2, hc2, tail⟩

theorem one_letter_gauss_every_integral_disc_seven : OneLetterGaussEveryInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨s2, hs2, hc2, fun σ hσ F hF => one_letter_gauss_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem one_letter_gauss_integral_disc_seven : OneLetterGaussInt7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, hs2, hc2, tail⟩ := one_letter_gauss_every_integral_disc_seven dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, hg, hε, hth, hs2, hc2, tail⟩

theorem ThmAEntryEveryPh7_of (hS : HypShape) : ThmAEntryEveryPh7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ f f' hH Θ hInt
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact matrix_entries_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

theorem matrix_entries_sharp_of_kappa_integral (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : MatrixEntriesSharpCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact matrix_entries_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

theorem ThmAEntryEveryOrth7_of (hS : OrthShape) : ThmAEntryEveryOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ f f' hH ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH ω₀ hω hω2 κ r s N
    hr hN0 hlN hs
  rw [hΘ]
  exact matrix_entries_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

theorem ThmAGaussEveryPh7_of (hS : HypShape) : ThmAGaussEveryPh7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ f f' hH Θ hInt
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact gauss_form_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

theorem gauss_form_sharp_of_kappa_integral (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : GaussFormSharpCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact gauss_form_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

theorem ThmAGaussEveryOrth7_of (hS : OrthShape) : ThmAGaussEveryOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev hN0' ιr _ _ om oms hO hT hζ n _ f f' hH ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) N0 N1 ιr n f f' hH ω₀ hω hω2 κ r s N
    hr hN0 hlN hs
  rw [hΘ]
  exact gauss_form_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev hN0' ιr om oms hO hT hζ U0 Φ hU hΦ hsim

namespace DiscriminantSevenGaussModels

theorem cc_phSum {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) (g2 g3 s2 ε : CM.MaximalUnramifiedExtension l) (n : Type) [Fintype n] :
    MvPowerSeries.constantCoeff
      (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) = 0 := by
  unfold Formalism.L2.Th1.E.phSum
  rw [map_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  refine Pair.constantCoeff_inVar_eq_zero x ?_
  unfold phL
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF (by omega), map_zero]

theorem split {l : ℕ} [Fact l.Prime] (h5 : 5 ≤ l) (g2 g3 s2 ε : CM.MaximalUnramifiedExtension l) (n : Type) [Fintype n]
    (Θ : MvPowerSeries n ℂ_[l]) :
    Θ = Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε)) * Θ) := by
  have h0 := cc_phSum h5 g2 g3 s2 ε n
  obtain ⟨e0, -, eadd, -⟩ := Formalism.L2.Th1.C.mvExpLaws ℂ_[l] n
  have h1 := eadd (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε))) (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε))
    (by rw [map_neg, h0, neg_zero]) h0
  rw [neg_add_cancel, e0] at h1
  rw [← mul_assoc]
  change Θ = (Formalism.L2.Th1.C.mvExp _ * Formalism.L2.Th1.C.mvExp _) * Θ
  rw [← h1, one_mul]

end DiscriminantSevenGaussModels

theorem one_letter_gauss_every_principal_seven : OneLetterGaussEveryPh7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF N0 N1 C Θ hInt
  rw [DiscriminantSevenGaussModels.split h5 g2 g3 s2 ε (Fin N0 × Fin N1) Θ]
  exact one_letter_gauss_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) N0 N1 C
    _ _ hInt (DiscriminantSevenGaussModels.cc_phSum h5 g2 g3 s2 ε _) (InverseCommuting.sim_refl _)

theorem one_letter_gauss_sharp_of_kappa_integral (hK : uniformGaussModelConditionReformulated) : OneLetterGaussSharpCM := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF N0 N1 C Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) (Fin N0 × Fin N1) Θ γ hγ hK1
  rw [DiscriminantSevenGaussModels.split h5 g2 g3 s2 ε (Fin N0 × Fin N1) Θ]
  exact one_letter_gauss_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) N0 N1 C
    _ _ hInt (DiscriminantSevenGaussModels.cc_phSum h5 g2 g3 s2 ε _) (InverseCommuting.sim_refl _)

theorem OneLetterGaussEveryOrth7_of (hS : OrthShapeOne) : OneLetterGaussEveryOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF N0 N1 C ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, hU, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth (Fin N0 × Fin N1) ω₀ hω hω2 κ r s N hr hN0 hlN hs
  rw [hΘ]
  exact one_letter_gauss_all_disc_seven l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) N0 N1 C
    U0 _ hU (DiscriminantSevenGaussModels.cc_phSum h5 g2 g3 s2 ε _) (InverseCommuting.sim_refl _)

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem ThmAEntryOrth7_of (h : ThmAEntryEveryOrth7) : ThmAEntryOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ := h dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, c, hc, hg, hε, hth, hs2, e2, e3, es, tail⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem ThmAGaussOrth7_of (h : ThmAGaussEveryOrth7) : ThmAGaussOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ := h dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, c, hc, hg, hε, hth, hs2, e2, e3, es, tail⟩

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem OneLetterGaussOrth7_of (h : OneLetterGaussEveryOrth7) : OneLetterGaussOrth7 := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l cm2 cm3 dK L hsq hd4 hcm h5 hd hin ι
  obtain ⟨s2, c, hc, hs2, e2, e3, es, tail⟩ := h dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨g2, g3, ε, s2, c, hc, hg, hε, hth, hs2, e2, e3, es, tail⟩

end Formalism.L2.Th1.Top
