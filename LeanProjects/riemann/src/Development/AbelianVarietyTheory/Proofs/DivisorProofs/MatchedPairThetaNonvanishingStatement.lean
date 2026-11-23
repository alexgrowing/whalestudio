import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaNonvanishing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_pair_theta_nonvanishing : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → ∀ (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ P : Submodule ℂ (SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M B.ψ B.emb om P → G.M.Pol B.ψ B.emb ⊓ N.comap (GlobalTheory.ThetaFacInf.pureL φ) ≤ P → P ≠ G.M.Pol B.ψ B.emb → P ≤ N.comap (GlobalTheory.ThetaFacInf.pureL φ) := by
  first | exact @GlobalTheory.ThetaFibMax.fibMax | exact GlobalTheory.ThetaFibMax.fibMax | (intros; apply GlobalTheory.ThetaFibMax.fibMax <;> assumption)
