import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleRealMapsForallPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleBaseCharacterConditionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleBaseAdditiveCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleFiniteMapsForallPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLocalComponentsAgreeStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem GlobalTheory.ThetaFacW.semisimple_alt : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ' ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Φ' ≠ 0 → ∃ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N ∧ (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Ψ = 0 → Ψ ∈ N) ∧ Φ' ∉ N := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ' hΦ' hI
  obtain ⟨N, hSt, hKN, hND, hxN, hmax⟩ := GlobalTheory.ThetaFacW.exists_max_not_mem (GlobalTheory.ThetaFac.WStable B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁))
    (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) _ (GlobalTheory.T.matched_triple_base_additive_character hK F E σ B a a' G X om om' R Rf hM)
    (Submodule.span_le.2 fun Ψ hΨ => hΨ.1) (GlobalTheory.ThetaFacW.wStable_sSup B om' _)
    (GlobalTheory.ThetaFacW.wStable_sup B om' _ (GlobalTheory.T.matched_triple_finite_maps_forall_places hK F E σ B a a' G X om om' R Rf hM))
    (GlobalTheory.T.matched_triple_local_components_agree hK F E σ B a a' G X om om' R Rf hM) Φ' hΦ' (fun h => hI (GlobalTheory.T.modelI_eq_zero_of_mem_span_polData_so_ker hK F E σ B a a' G X om om' R Rf hM Φ' h))
  exact ⟨N, ⟨hND, fun h => hxN (h ▸ hΦ'), GlobalTheory.ThetaFacW.CoinvLe.mono (GlobalTheory.T.matched_triple_base_character_condition hK F E σ B a a' G X om om' R Rf hM) hKN, hSt,
    fun N' h1 h2 h3 => hmax N' h1 h2 h3⟩, fun Ψ hΨ h0 => hKN (Submodule.subset_span ⟨hΨ, h0⟩), hxN⟩
