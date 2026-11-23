import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthShapeOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (cm4)

theorem ThmSEveryInt_proof : ThmSEveryInt := by
  intro dK L hsq hd4 hcm l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ :=
    nrcmOfCM4 cm4 dK L hsq hd4 hcm l h5 hd hin ι g2 g3 ε hg hε hth
  refine ⟨s2, c, hc, hs2, e2, e3, es, ?_⟩
  intro σ hσ F hF ν r0 r1 _
  obtain ⟨a1, a2, -⟩ := FAux.ffs l first_level_on_curve g2 g3 ε hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF s2 (hN σ hσ)
  have : CompleteSpace (CM.MaximalUnramifiedExtension l) := kurComplete l
  exact thmSOfF (CM.MaximalUnramifiedExtension l) ℂ_[l] (CM.MaximalUnramifiedExtension l).subtype l ν r0 r1 σ (FAux.norm_coe l) hσ (FAux.exists_root2 l)
    F hF _ a1 a2

theorem ThmSEveryOrth_of (hS : OrthShape) : ThmSEveryOrth := by
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
  intro om oms ϖ μ hϖ hO hT hμ0 hμ n _ f f' hH ω₀ hω hω2 κ _ r s N hr hN0 hlN hs
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 (Formalism.L2.Th1.F.scalePair L c hc) ι g2 g3 ε s2 e2 e3 es
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) r0 r1 (Fin ν) n f f' hH ω₀ hω hω2 κ r s N
    hr hN0 hlN hs
  rw [hΘ]
  exact h3 om oms ϖ μ U0 Φ hϖ hO hT hμ0 hμ hU hΦ hsim

theorem structureTheoremCM_of_uniformGaussModels_of_hypShape (hK : uniformGaussModelConditionReformulated) (hS : HypShape) : StructureTheoremCM := by
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
  intro om oms ϖ μ hϖ hO hT hμ0 hμ n _ _ f f' hH Θ γ hγ hK1
  have hInt := hK l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n Θ γ hγ hK1
  obtain ⟨U0, Φ, hU, hΦ, hsim, hΘ⟩ := hS l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ)
    r0 r1 (Fin ν) n f f' hH Θ hInt
  rw [hΘ]
  exact h3 om oms ϖ μ U0 Φ hϖ hO hT hμ0 hμ hU hΦ hsim

end Formalism.L2.Th1.Top
