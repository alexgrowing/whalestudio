import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleAdaptedScalar
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_triple_adapted_scalar : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → ∀ (f : SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ), f ∈ G.M.Pol B.ψ B.emb → (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ v, Rf.p v (φ v) = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N := by
  first | exact @GlobalTheory.ThetaKillFin.killFin | exact GlobalTheory.ThetaKillFin.killFin | (intros; apply GlobalTheory.ThetaKillFin.killFin <;> assumption)
