import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleArchimedeanComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleNonarchimedeanComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalProductFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleUnramifiedTestVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLocalIntegralNonzeroStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.KerStabW

theorem kerStab : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → GlobalTheory.ThetaFac.WStable B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) (Submodule.span ℂ {Ψ | Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0}) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  have hI : ∀ (h : UA σ G.W.J) (Ψ : Fn F a' (a + a')) (h₀ : UA σ G.W.J),
      G.M'.I om' (om' (1, h) Ψ) h₀ = G.M'.I om' Ψ (h₀ * h) := by
    intro h Ψ h₀
    unfold Model.I theta
    congr 1
    funext g
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have key : ∀ h : UA σ G.W.J, (∀ Ψ ∈ PolData B G.M', om' (1, h) Ψ ∈ PolData B G.M') →
      (∀ Ψ ∈ G.M'.So B.ψ B.τ₁, om' (1, h) Ψ ∈ G.M'.So B.ψ B.τ₁) →
      ∀ Φ ∈ Submodule.span ℂ {Ψ | Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0},
        om' (1, h) Φ ∈ Submodule.span ℂ {Ψ | Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0} := by
    intro h hP hS Φ hΦ
    have hle : Submodule.span ℂ {Ψ | Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0} ≤
        (Submodule.span ℂ {Ψ | Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0}).comap (om' (1, h)) := by
      refine Submodule.span_le.2 ?_
      rintro Ψ ⟨⟨hΨP, hΨS⟩, hΨI⟩
      refine Submodule.subset_span ⟨⟨hP Ψ hΨP, hS Ψ hΨS⟩, ?_⟩
      funext h₀
      rw [hI, hΨI]
      rfl
    exact hle hΦ
  refine ⟨?_, ?_, ?_⟩
  · intro v h hh Φ hΦ
    exact key h (GlobalTheory.T.matched_triple_archimedean_components hKP F E σ B a a' G X om om' R Rf hM v h hh)
      (GlobalTheory.T.matched_triple_nonarchimedean_components hKP F E σ B a a' G X om om' R Rf hM v h hh) Φ hΦ
  · intro γ hγ Φ hΦ Φ₁ hΦ₁ hd
    exact Submodule.subset_span ⟨hΦ₁, GlobalTheory.T.matched_triple_local_integral_nonzero hKP F E σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hΦ₁ hd⟩
  · intro k hk Φ hΦ
    exact key k (GlobalTheory.T.om_kInf_mem_polData_of_isMatched hKP F E σ B a a' G X om om' R Rf hM k hk)
      (GlobalTheory.T.matched_triple_unramified_test_vector hKP F E σ B a a' G X om om' R Rf hM k hk) Φ hΦ

end GlobalTheory.KerStabW
