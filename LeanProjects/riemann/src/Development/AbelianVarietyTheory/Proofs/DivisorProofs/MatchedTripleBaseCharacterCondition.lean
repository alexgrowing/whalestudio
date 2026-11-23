import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleFiniteWeilIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLatticeVectorIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleCasimirCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaComparisonStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThetaFac

theorem coinvLe_span_ker : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → GlobalTheory.ThetaFac.CoinvLe B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) (Submodule.span ℂ {Ψ | Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0}) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  have hFin := GlobalTheory.T.matched_triple_finite_weil_identity hK F E σ B a a' G X om om' R Rf hM
  have hCpt := GlobalTheory.T.matched_triple_lattice_vector_identity hK F E σ B a a' G X om om' R Rf hM
  have hSub := GlobalTheory.T.matched_triple_casimir_compatible hK F E σ B a a' G X om om' R Rf hM
  have hTr := GlobalTheory.T.matched_pair_theta_lattice_sum hK F E σ B a a' G X om om' R Rf hM
  have hLie := GlobalTheory.T.modelI_eq_zero_of_hasDerivAt_line hK F E σ B a a' G X om om' R Rf hM
  refine ⟨?_, ?_, ?_⟩
  · intro v g hg Φ hΦ
    refine Submodule.subset_span ⟨Submodule.sub_mem _ (hFin v g hg Φ hΦ) hΦ, ?_⟩
    rw [hSub _ (hFin v g hg Φ hΦ) _ hΦ, hTr g Φ hΦ, sub_self]
  · intro γ hγ Φ hΦ Φ₁ hΦ₁ hd
    exact Submodule.subset_span ⟨hΦ₁, hLie γ hγ Φ hΦ Φ₁ hΦ₁ hd⟩
  · intro k hk Φ hΦ
    refine Submodule.subset_span ⟨Submodule.sub_mem _ (hCpt k hk Φ hΦ) hΦ, ?_⟩
    rw [hSub _ (hCpt k hk Φ hΦ) _ hΦ, hTr k Φ hΦ, sub_self]

end GlobalTheory.ThetaFac
