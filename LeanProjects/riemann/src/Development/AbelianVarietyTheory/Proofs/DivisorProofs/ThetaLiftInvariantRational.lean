import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst

noncomputable section

namespace GlobalTheory.ThK.LeftInvV

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.WeilM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem polData_le_schA {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, hφ, hv, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hφ ((hv.and hM.std).mono fun v h => h.1.trans h.2)

theorem symm_mem_ratU {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0)
    {γ : GAd σ (c • J.map σ)} (hγ : γ ∈ ratPts σ (c • J.map σ)) : (toGAd hσ J hc).symm γ ∈ ratU σ J := by
  obtain ⟨u, -, hu⟩ := hγ
  exact ⟨u, hu⟩

theorem left_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∀ γ ∈ ratPts σ (c • G.W.J.map σ), ∀ g, G.M.I om Φ ((toGAd hσ G.W.J hc).symm (γ * g)) = G.M.I om Φ ((toGAd hσ G.W.J hc).symm g) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc _ Φ hΦ γ hγ g
  have hB := GlobalTheory.T.theta_basic_properties hKP.base
  have hP := GlobalTheory.ThKConst.isPair_big hT
  obtain ⟨-, hinv, -⟩ := (hB F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP).1 Φ
    (polData_le_schA hT.geo.hM hΦ)
  rw [map_mul]
  unfold Model.I
  congr 1
  funext x
  simpa using hinv 1 (one_mem _) _ (symm_mem_ratU hσ G.W.J hc hγ) x ((toGAd hσ G.W.J hc).symm g)

end GlobalTheory.ThK.LeftInvV
