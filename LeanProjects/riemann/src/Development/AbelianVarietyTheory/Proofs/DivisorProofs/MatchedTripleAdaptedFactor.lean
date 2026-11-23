import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperThetaSubmoduleInKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaNonvanishingStatement

noncomputable section

namespace GlobalTheory.ThetaFacInf

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

theorem pure_mem_of_realKer : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → ∀ (f : SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ), f ∈ G.M.Pol B.ψ B.emb → (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → R.p f = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN _hI f φ hf hφ hφc hp
  set Pol := G.M.Pol B.ψ B.emb with hPol
  have hK := GlobalTheory.T.matched_pair_theta_identity hKP F E σ B a a' G X om om' R Rf hM
  have hKne : Pol ⊓ LinearMap.ker R.p ≠ Pol := by
    intro h
    haveI := hM.real.nontriv
    have hon := hM.real.quot.onto
    have h0 : Submodule.map R.p Pol = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨g, hg, rfl⟩
      have : g ∈ Pol ⊓ LinearMap.ker R.p := by rw [h]; exact hg
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2)
    exact bot_ne_top (h0.symm.trans hon)
  have hfK : f ∈ Pol ⊓ LinearMap.ker R.p := Submodule.mem_inf.2 ⟨hf, LinearMap.mem_ker.2 hp⟩
  have key : f ∈ N.comap (GlobalTheory.ThetaFacInf.pureL φ) := by
    by_cases hF : Pol ⊓ N.comap (GlobalTheory.ThetaFacInf.pureL φ) = Pol
    · have : f ∈ Pol ⊓ N.comap (GlobalTheory.ThetaFacInf.pureL φ) := by rw [hF]; exact hf
      exact (Submodule.mem_inf.1 this).2
    · have hle : Pol ⊓ N.comap (GlobalTheory.ThetaFacInf.pureL φ) ≤ Pol ⊓ LinearMap.ker R.p :=
        le_inf inf_le_left (GlobalTheory.T.matched_pair_theta_convergence hKP F E σ B a a' G X om om' R Rf hM _
          (GlobalTheory.T.matched_pair_theta_vanishing hKP F E σ B a a' G X om om' R Rf hM N hN φ hφ hφc) hF)
      exact GlobalTheory.T.matched_pair_theta_nonvanishing hKP F E σ B a a' G X om om' R Rf hM N hN φ hφ hφc _ hK hle hKne hfK
  exact key

end GlobalTheory.ThetaFacInf

end
