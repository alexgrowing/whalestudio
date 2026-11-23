import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropertyOfCodimOneLocalUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOpenNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapCompatibilityStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem genSt_of_hypotheses : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
    GenSt := by
  intro h1 h2 h3 E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A _ _ _ ξ β hξ hβ hpu hgen
    g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂
  haveI := GlobalTheory.T.integral_model_open_noetherian E H Dw l' Xo' c' W Y A ξ hξ
  obtain ⟨f, hf⟩ := GlobalTheory.T.property_of_codim_one_local_units A (SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂) {𝔭 | ξ 𝔭 ∈ Set.range Y.j} (hC.2.2.2.2.1 hgen)
    (fun 𝔭 h𝔭 => by
      by_cases hg : ξ 𝔭 ∈ Set.range Y.j
      · exact GlobalTheory.T.integral_model_map_extension h1 h2 h3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A ξ β hξ hβ hpu hgen
          g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂ 𝔭 hg
      · exact GlobalTheory.T.integral_model_map_uniqueness h1 h2 h3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A ξ β hξ hβ hpu hgen
          g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂ 𝔭 (h𝔭.resolve_left hg) hg)
    (GlobalTheory.T.integral_model_map_compatibility h1 h2 h3 E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hC A ξ β hξ hβ hpu hgen
                   g e U₁ h₁ U₂ h₂ hT hE hd₁ hd₂)
    (fun k _ φ v hv inst yy hyy => by
      exfalso
      apply hv
      refine ⟨yy (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), ?_⟩
      have e1 : (yy ≫ Y.j) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) =
          (spMap φ ≫ ξ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) := by rw [hyy]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans
        (e1.trans ((Scheme.Hom.comp_apply _ _ _).trans (congrArg ξ (PrimeSpectrum.ext rfl)))))
  exact ⟨f, fun k _ _ φ yy hyy => hf k φ _ yy hyy⟩
end GlobalTheory.FlatModel
end
