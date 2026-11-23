import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemiMeasIsMulLeftInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemiMeasFiniteOnCompactsAndOpenPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicProjectionUnitaryInvEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagStabilizerAnisotropicBlockExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapConjSmallerUnitaryFlagUnipotentHaar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MixPer

theorem jacGrp_besGrp_haar : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ν : Measure (flagN d)) (𝓝 : Set (flagN d)), GlobalTheory.Per.IsUnitN S d.e ν 𝓝 → (IsClosed (jacGrp d : Set (GA D S)) ∧ ∀ μ : Measure (GA D S₀), μ.IsHaarMeasure → (semiMeas (flagN d) d.emb0 μ ν).IsHaarMeasure) ∧ IsClosed (besGrp d o : Set (GA D S)) ∧ ∀ μ : Measure (GA D A), μ.IsHaarMeasure → (semiMeas (flagN d) (embA d o) μ ν).IsHaarMeasure := by
  intro D S S₀ A L ρ d o ν 𝓝 hν
  have hNc : IsClosed (flagN d : Set (GA D S)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag S (isIsoSub_e d)
  have hνH : ν.IsHaarMeasure := hν.1
  have hcA : Continuous (embA d o) := by
    have h1 : Continuous (fun h : GA D A => o.emb (h, 1)) := by
      have := o.continuous_emb
      fun_prop
    exact d.continuous_embed.comp h1
  have hnA : ∀ n ∈ flagN d, ∀ h, embA d o h * n * (embA d o h)⁻¹ ∈ flagN d := fun n hn h =>
    GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn (o.emb (h, 1))
  have hmA : ∀ h, ν.map (fun n : flagN d => embA d o h * n.1 * (embA d o h)⁻¹) = ν.map Subtype.val := fun h =>
    GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH (o.emb (h, 1))
  refine ⟨⟨GlobalTheory.jacGrp_isClosed D S S₀ ρ d, fun μ hμ => ?_⟩, GlobalTheory.BesClosed.besGrp_isClosed D S S₀ A L ρ d o, fun μ hμ => ?_⟩
  · have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) d.emb0 hNc d.continuous_embed (GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d) (GlobalTheory.JacProj.exists_continuous_proj D S S₀ ρ d) μ ν hμ hνH
      (GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH)
    obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) d.emb0 hNc d.continuous_embed (GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d) (GlobalTheory.JacProj.exists_continuous_proj D S S₀ ρ d) μ ν hμ hνH
      (GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D S S₀ ρ d ν hνH)
    exact { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }
  · have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) (embA d o) hNc hcA hnA (GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o) μ ν hμ hνH hmA
    obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) (embA d o) hNc hcA hnA (GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o) μ ν hμ hνH hmA
    exact { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }

end GlobalTheory.MixPer

end
