import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.OneLetterGaussFinal

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

theorem theorem_a_entry_all : ThmAEntryAll := by
  intro l _ _ g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  exact thmAEntryOfF l (MaximalUnramifiedExtension l) σ hσ (MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2

theorem theorem_a_gauss_all : ThmAGaussAll := by
  intro l _ _ g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  exact thmAGaussOfF l (MaximalUnramifiedExtension l) σ hσ (MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2

theorem one_letter_gauss_all : OneLetterGaussAll := by
  intro l _ _ g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨a1, a2, a3⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  exact oneLetterGaussOfF l (MaximalUnramifiedExtension l) σ hσ (MaximalUnramifiedExtension l).subtype (FAux.norm_coe l) F hF _ a1 a2
    (FAux.exists_root2 l) _ a3

theorem kernel_all : KernelAll := by
  intro l _ _ g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN ν r0 r1 _ om oms
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  have : CompleteSpace (MaximalUnramifiedExtension l) := kurComplete l
  exact kernelOfF l (MaximalUnramifiedExtension l) σ hσ (FAux.exists_root2 l) F hF _ a1 a2 ℂ_[l] (MaximalUnramifiedExtension l).subtype ν r0 r1
    (FAux.norm_coe l) (FAux.exists_pi l) om oms

theorem ThmAEntryFinal_of' (hNR : Formalism.L2.Th1.CM.CM4 → NRCM) : ThmAEntryFinal := by
  intro h2 h3 h4' dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  obtain ⟨s2, hs2, hc2, hN⟩ := hNR h4' dK L hsq h4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨g2, g3, ε, s2, hg, hε, hth, hs2, hc2, ?_⟩
  intro σ hσ F hF
  exact theorem_a_entry_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)

theorem ThmAGaussFinal_of' (hNR : Formalism.L2.Th1.CM.CM4 → NRCM) : ThmAGaussFinal := by
  intro h2 h3 h4' dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  obtain ⟨s2, hs2, hc2, hN⟩ := hNR h4' dK L hsq h4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨g2, g3, ε, s2, hg, hε, hth, hs2, hc2, ?_⟩
  intro σ hσ F hF
  exact theorem_a_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)

theorem OneLetterGaussFinal_of' (hNR : Formalism.L2.Th1.CM.CM4 → NRCM) : OneLetterGaussFinal := by
  intro h2 h3 h4' dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  obtain ⟨s2, hs2, hc2, hN⟩ := hNR h4' dK L hsq h4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨g2, g3, ε, s2, hg, hε, hth, hs2, hc2, ?_⟩
  intro σ hσ F hF
  exact one_letter_gauss_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)

theorem KernelFinal_of' (hNR : Formalism.L2.Th1.CM.CM4 → NRCM) : KernelFinal := by
  intro h2 h3 h4' dK L hsq h4 hcm l _ h5 hd hin ι
  obtain ⟨g2, g3, ε, hg, hε, hth⟩ := FAux.model l h2 h3 dK L hsq h4 hcm h5 hd hin ι
  obtain ⟨s2, hs2, hc2, hN⟩ := hNR h4' dK L hsq h4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨g2, g3, ε, s2, hg, hε, hth, hs2, hc2, ?_⟩
  intro σ hσ F hF
  exact kernel_all l h5 g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)

end Formalism.L2.Th1.D
