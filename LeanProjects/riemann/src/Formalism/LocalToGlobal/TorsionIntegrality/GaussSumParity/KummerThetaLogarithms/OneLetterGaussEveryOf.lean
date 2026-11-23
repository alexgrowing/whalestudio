import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.OneLetterGaussEvery
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.OneLetterGaussFinalOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.NRCMOf

namespace Formalism.L2.Th1.D

theorem ThmAEntryEvery_of (hNR : Formalism.L2.Th1.CM.CM4 → NRCM) : ThmAEntryEvery := by
  intro h4 dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ := hNR h4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨s2, hs2, hc2, fun σ hσ F hF =>
    theorem_a_entry_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)⟩

theorem ThmAGaussEvery_of (hNR : Formalism.L2.Th1.CM.CM4 → NRCM) : ThmAGaussEvery := by
  intro h4 dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ := hNR h4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨s2, hs2, hc2, fun σ hσ F hF =>
    theorem_a_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)⟩

theorem OneLetterGaussEvery_of (hNR : Formalism.L2.Th1.CM.CM4 → NRCM) : OneLetterGaussEvery := by
  intro h4 dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ := hNR h4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨s2, hs2, hc2, fun σ hσ F hF =>
    one_letter_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)⟩

theorem KernelEvery_of (hNR : Formalism.L2.Th1.CM.CM4 → NRCM) : KernelEvery := by
  intro h4 dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, hc2, hN⟩ := hNR h4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  exact ⟨s2, hs2, hc2, fun σ hσ F hF =>
    kernel_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)⟩

end Formalism.L2.Th1.D
