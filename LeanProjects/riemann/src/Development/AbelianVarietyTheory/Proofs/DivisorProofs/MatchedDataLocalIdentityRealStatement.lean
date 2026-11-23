import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDataLocalIdentityReal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUpdate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_data_local_identity_real : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → ∀ v : Pl F, ∀ w : Pl F, ∀ h ∈ UAt σ G.W (GlobalTheory.AdelicU.evFin F w), ∀ Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om' v) N (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), om' (1, h) Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om' v) N (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) := by
  first | exact @GlobalTheory.ThKSocFinW.socleOver_stable | exact GlobalTheory.ThKSocFinW.socleOver_stable | (intros; apply GlobalTheory.ThKSocFinW.socleOver_stable <;> assumption)
