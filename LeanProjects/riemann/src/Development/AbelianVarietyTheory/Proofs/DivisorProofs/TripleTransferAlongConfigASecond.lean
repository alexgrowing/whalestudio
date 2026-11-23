import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawIdentityConfigAFourthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTransferOfPlaneConfigStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSchwartzDenseOfTripleStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

namespace GlobalTheory.ThK

theorem nzInf_exists_pol : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))),
      IsNormK K (evI F) μK → μ.IsHaarMeasure →
    ∀ l : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ, l ≠ 0 →
      (∀ g ∈ UAt σ G₁.V (evI F), ∀ f f₁ : SInf F (Fin b × Fin (b + a')), Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f) →
      ∃ f ∈ G.M.Pol B.ψ B.emb, l (coneInf B G.M om ei K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) f) ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hei hev hpe K hK μK μ hμK hμ l hl hinv
  obtain ⟨T, hTf⟩ := GlobalTheory.T.seesaw_identity_config_a_fourth hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hei hev hpe K hK μK μ
    hμK hμ
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.triple_transfer_of_plane_config hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e he ei ev hei hev hpe K hK μK μ
    hμK hμ l hl hinv T hTf
  have hco : ∀ f, coneInf B G.M om ei K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) f = T f := fun f => coneInf_eq (hTf f)
  by_contra hne
  push_neg at hne
  have hD := GlobalTheory.T.polynomial_schwartz_dense_of_triple F E σ B (b + 2) a' G X om om' hT
  have hsub : ((G.M.Pol B.ψ B.emb : Submodule ℂ _) : Set (SInf F (Fin (b + 2) × Fin (b + 2 + a')))) ⊆
      {f | (l.comp T) f = 0} := fun f hf => by
    simp only [Set.mem_setOf_eq, ContinuousLinearMap.comp_apply, ← hco]
    exact hne f hf
  have hcl : IsClosed {f : SInf F (Fin (b + 2) × Fin (b + 2 + a')) | (l.comp T) f = 0} :=
    isClosed_eq (l.comp T).continuous continuous_const
  have h := closure_minimal hsub hcl
  rw [hD.closure_eq] at h
  exact hf₀ (h (Set.mem_univ f₀))

end GlobalTheory.ThK
