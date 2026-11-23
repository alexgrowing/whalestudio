import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalThetaFactorization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_theta_factorization : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → ∀ (f : SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ), f ∈ G.M.Pol B.ψ B.emb → (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∉ N → ∀ v : Pl F, ∃ P : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ), Maximal (fun Q => GlobalTheory.Published.ThetaSub om v Q ∧ Q ≠ SB _) P ∧ φ v ∉ P := by
  first | exact @GlobalTheory.ThetaRadZero.radZero | exact GlobalTheory.ThetaRadZero.radZero | (intros; apply GlobalTheory.ThetaRadZero.radZero <;> assumption)
