import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsIsCharAF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStdMulShift
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PsiUnrOfNotLe

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

theorem baseEx : BaseEx := by
  intro F E _ _ _ _ _ σ hc emb mα mβ
  obtain ⟨ψ₀, hψ₀⟩ := GlobalTheory.CompanionTheory.SW.CharEx.exists_isCharAF F
  obtain ⟨a, -, ha⟩ := GlobalTheory.StdRescale.exists_isStd_mulShift F hc.1 ψ₀ hψ₀
  obtain ⟨v₁, -, ⟨τ₁⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem hc ∅
  refine ⟨⟨ψ₀.mulShift (algebraMap F (AF F) a), emb, mα, mβ, ∅,
    fun v => absurd v.2 (Finset.notMem_empty _), v₁, τ₁⟩, rfl, rfl, rfl, rfl, ha, fun hu hg => ?_⟩
  exact
    { cm := hc
      galois := hg.1
      unram := hu
      std := ha
      inert := fun v w h => by
        obtain ⟨h2, h3, hd⟩ := hg.2 v w h
        exact ⟨h2, h3, PositivityTheory.Mix.psiUnr_of_not_le ha v hd⟩
      psiP := fun v hv => absurd hv (Finset.notMem_empty _) }

end UpperTheory.Gal.TP.Skew

end
