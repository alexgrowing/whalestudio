import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementG
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SecondCoeffConsistency

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (cm4)

theorem ThmAEntryEveryPh_of (hS : HypShape) : ThmAEntryEveryPh := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev ιr _ _ om oms hO hT hζ n _ f f' hH Θ hInt
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact theorem_a_entry_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev ιr om oms hO hT hζ
    U0 Φ hU hΦ hsim

theorem ThmAGaussEveryPh_of (hS : HypShape) : ThmAGaussEveryPh := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF d N0 N1 _ hd2 hev ιr _ _ om oms hO hT hζ n _ f f' hH Θ hInt
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    N0 N1 ιr n f f' hH Θ hInt
  rw [hΘ]
  exact theorem_a_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) d N0 N1 hd2 hev ιr om oms hO hT hζ
    U0 Φ hU hΦ hsim

theorem KernelEveryPh_of (hS : HypShape) : KernelEveryPh := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF ν r0 r1 _ om oms hO hT n _ f f' hH Θ hInt
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    r0 r1 (Fin ν) n f f' hH Θ hInt
  rw [hΘ]
  exact kernel_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) ν r0 r1 om oms hO hT
    U0 Φ hU hΦ hsim

theorem one_letter_gauss_every_ph : OneLetterGaussEveryPh := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, hs2, hc2, ?_⟩
  intro σ hσ F hF N0 N1 C Θ hInt
  have h0 : MvPowerSeries.constantCoeff
      (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries (Fin N0 × Fin N1) ℂ_[l]) = 0 := by
    unfold Formalism.L2.Th1.E.phSum
    rw [map_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    refine Pair.constantCoeff_inVar_eq_zero x ?_
    unfold phL
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, FAux.cc_phFF (by omega), map_zero]
  have hΘ : Θ = Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) :
      MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε)) * Θ) := by
    obtain ⟨e0, -, eadd, -⟩ := Formalism.L2.Th1.C.mvExpLaws ℂ_[l] (Fin N0 × Fin N1)
    have h1 := eadd (-(Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε))) (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε))
      (by rw [map_neg, h0, neg_zero]) h0
    rw [neg_add_cancel, e0] at h1
    rw [← mul_assoc]
    change Θ = (Formalism.L2.Th1.C.mvExp _ * Formalism.L2.Th1.C.mvExp _) * Θ
    rw [← h1, one_mul]
  rw [hΘ]
  exact one_letter_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ) N0 N1 C
    _ _ hInt h0 (InverseCommuting.sim_refl _)

theorem ThmSEveryPh_of (hS : HypShape) : ThmSEveryPh := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF ν r0 r1 _
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)
  have : CompleteSpace (CM.MaximalUnramifiedExtension l) := kurComplete l
  obtain ⟨cS, h1, h2, h3⟩ := thmSOfF (CM.MaximalUnramifiedExtension l) ℂ_[l] (CM.MaximalUnramifiedExtension l).subtype l ν r0 r1 σ (FAux.norm_coe l) hσ
    (FAux.exists_root2 l) F hF _ a1 a2
  refine ⟨cS, h1, h2, ?_⟩
  intro om oms ϖ μ hϖ hO hT hμ0 hμ n _ f f' hH Θ hInt
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    r0 r1 (Fin ν) n f f' hH Θ hInt
  rw [hΘ]
  exact h3 om oms ϖ μ U0 Φ hϖ hO hT hμ0 hμ hU hΦ hsim

end Formalism.L2.Th1.Top
