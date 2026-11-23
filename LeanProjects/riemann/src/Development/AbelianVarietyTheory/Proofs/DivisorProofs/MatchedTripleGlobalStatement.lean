import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleRealWeilIdentityStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThetaDerivZero

theorem hasDerivAt_transl : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Φ₁ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, HasDerivAt (fun t : ℝ => G.M'.I om' Φ (h * γ (Multiplicative.ofAdd t))) (G.M'.I om' Φ₁ h) 0 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hΦ₁ hd h
  have e : (fun t : ℝ => G.M'.I om' Φ (h * γ (Multiplicative.ofAdd t))) =
      fun t : ℝ => G.M'.I om' (om' (1, γ (Multiplicative.ofAdd t)) Φ) h := by
    funext t
    unfold Model.I theta
    congr 1
    funext g
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  rw [e]
  exact GlobalTheory.T.matched_triple_real_weil_identity hP F E σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hΦ₁ hd h

end GlobalTheory.ThetaDerivZero

end
