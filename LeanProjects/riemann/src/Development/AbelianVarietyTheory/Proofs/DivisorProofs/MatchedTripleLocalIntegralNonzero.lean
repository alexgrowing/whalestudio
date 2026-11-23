import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleRealMapsForallPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleRealWeilIdentityStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.LieKer

theorem I_translate {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (k h : UA σ W.J) :
    M.I om (om (1, k) Φ) h = M.I om Φ (h * k) := by
  unfold Model.I theta
  congr 1
  funext g
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

end GlobalTheory.ThK.LieKer

namespace GlobalTheory.ThK.LieKer

theorem lieDeriv_I_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ γ ∈ Lines σ G.W, ∀ Φ ∈ Submodule.span ℂ {Ψ | Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' Ψ = 0}, ∀ Φ₁ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → G.M'.I om' Φ₁ = 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hΦ₁ hder
  have hΦD : Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ :=
    (Submodule.span_le.2 (fun Ψ hΨ => hΨ.1)) hΦ
  have h0 : G.M'.I om' Φ = 0 := GlobalTheory.T.modelI_eq_zero_of_mem_span_polData_so_ker hKP F E σ B a a' G X om om' R Rf hM Φ hΦ
  funext h
  have hd := GlobalTheory.T.matched_triple_real_weil_identity hKP F E σ B a a' G X om om' R Rf hM γ hγ Φ hΦD Φ₁ hΦ₁ hder h
  have hc : (fun t : ℝ => G.M'.I om' (om' (1, γ (Multiplicative.ofAdd t)) Φ) h) = fun _ => 0 := by
    funext t
    rw [I_translate, h0]
    rfl
  rw [hc] at hd
  exact (hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))).trans rfl

end GlobalTheory.ThK.LieKer
