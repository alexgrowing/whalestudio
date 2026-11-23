import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiFactorsLocalFlatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzLinearStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapDualColumnMultiplicationLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatBesselToFourierJacobiRowMulLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFreeEntryTranslationLawsBesselToJacoStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFlatMapLocalUnipotentTranslationLawStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorValuesThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesTranslationsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesMultiplicationStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatBFLoc

theorem flatBF_of_laws : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatBF D := by
  intro D hFL hFLs hOm k _ _ _ _ _ _ p ν hν ψ ψk hψk ρ B J st s hs n n' _ _ _ _ c FA F₀ FV G₀ FW hco hbe hja Tm hTm
  obtain ⟨hcont, hne⟩ := (GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ st.weil.std).2.1 ψk hψk
  have hc : c = 2 * ρ := by have := hbe.1; omega
  let L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ) :=
    { toFun := fun Φ => flatBF st (Tm Φ)
      map_add' := fun Φ Φ' => by
        simp only [map_add]
        exact (GlobalTheory.T.besselToJacobiFlatSchwartz_linear D hFL ψ ρ B J st (Tm Φ) (Tm Φ') 1 (hTm.theta Φ) (hTm.theta Φ')).1
      map_smul' := fun a Φ => by
        simp only [map_smul, RingHom.id_apply]
        exact (GlobalTheory.T.besselToJacobiFlatSchwartz_linear D hFL ψ ρ B J st (Tm Φ) (Tm Φ) a (hTm.theta Φ) (hTm.theta Φ)).2 }
  obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.flatMap_fourierJacobi_factors_local_flat k ψk ν hcont hne hν n n' c ρ (WO B.V₀ J.W₀ → ℂ) L hc
    (GlobalTheory.T.localFlatMap_dualColumn_multiplicationLaws D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (GlobalTheory.T.flat_bessel_to_fourierJacobi_row_mul_laws D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (GlobalTheory.T.localFlatMap_freeEntry_translationLaws_besselToJacobi D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
    (GlobalTheory.T.besselFlatMap_local_unipotent_translation_law D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm)
  have hL : ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ := hL₀
  refine ⟨L₀, ⟨?_, ?_, ?_⟩, hL⟩
  · exact GlobalTheory.T.localFlatMap_factor_values_thetaFunctions D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL
  · exact GlobalTheory.T.localFlatMap_factor_intertwines_translations D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL
  · exact GlobalTheory.T.localFlatMap_factor_intertwines_multiplication D hFL hFLs hOm k p ν hν ψ ψk hψk ρ B J st s hs n n' c FA F₀ FV G₀ FW hco hbe hja Tm hTm L₀ hL

end GlobalTheory.FlatBFLoc
end
