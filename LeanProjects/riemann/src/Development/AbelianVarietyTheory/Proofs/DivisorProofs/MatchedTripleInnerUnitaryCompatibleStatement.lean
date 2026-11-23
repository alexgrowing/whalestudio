import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleInnerUnitaryCompatible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_triple_inner_unitary_compatible : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Ψ₂ ∈ GlobalTheory.ThK.PolData B G.M, ∀ c : ℂ, G.M.I om (Ψ₁ + Ψ₂) = G.M.I om Ψ₁ + G.M.I om Ψ₂ ∧ G.M.I om (c • Ψ₁) = c • G.M.I om Ψ₁ := by
  first | exact @GlobalTheory.ThKLinV.thetaIntegral_linear | exact GlobalTheory.ThKLinV.thetaIntegral_linear | (intros; apply GlobalTheory.ThKLinV.thetaIntegral_linear <;> assumption)
