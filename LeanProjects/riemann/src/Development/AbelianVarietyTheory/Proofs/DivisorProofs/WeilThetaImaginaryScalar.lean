import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDerivativeLineWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCountableRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRealLineDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataThetaLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUpdate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelDecay

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.ZFinSmallStab

open GlobalTheory.ThetaFacInf GlobalTheory.ThetaFacInf.Fib

theorem I_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (om : Rep σ Y W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (k x : UA σ W.J) : M.I om (om (1, k) Φ) x = M.I om Φ (x * k) := by
  simp only [Model.I, theta]
  congr 1
  funext g
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem span_theta_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c →
    ∀ (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      (∀ ψ ∈ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)}), IsSm σ (c • G.W.J.map σ) ψ) ∧ (∀ β, IsRealLine σ (c • G.W.J.map σ) β → ∀ ψ ∈ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)}), lineDer β ψ ∈ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)})) ∧
      (∀ k ∈ KInf σ G.W B.emb, ∀ ψ ∈ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)}), (fun x => ψ (x * toGAd hσ G.W.J hc k)) ∈ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)})) ∧
      Module.rank ℂ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)}) ≤ Cardinal.aleph0 := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcc φ hSB hev h1
  have hp := GlobalTheory.KDecayProof.isPair_small hT
  have hs : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2
  have hD : ∀ f ∈ G.M'.Pol B.ψ B.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ := fun f hf =>
    GlobalTheory.SoPure.pure_mem_polSo B G.M' hT.geo.hM'.std f hf φ hSB hev (Submodule.subset_span h1)
  obtain ⟨L, hL⟩ := GlobalTheory.T.pol_data_theta_linear F E σ B a a' G X om om' hKP hT
  let P : G.M'.Pol B.ψ B.emb →ₗ[ℂ] ↥(PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) :=
    ((pureL φ).domRestrict _).codRestrict _ (fun g => hD g.1 g.2)
  let T : G.M'.Pol B.ψ B.emb →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ L ∘ₗ P
  have eT : ∀ g : G.M'.Pol B.ψ B.emb,
      T g = fun x => G.M'.I om' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g.1 φ) ((toGAd hσ G.W.J hc).symm x) := fun g => by
    funext x
    show L (P g) _ = _
    rw [hL]
    rfl
  have eS : Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
      ψ = fun x => G.M'.I om' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ((toGAd hσ G.W.J hc).symm x)} = LinearMap.range T := by
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, eT _⟩
    · rintro _ ⟨g, rfl⟩
      exact Submodule.subset_span ⟨g.1, g.2, eT g⟩
  obtain ⟨-, -, hP3, hP4⟩ := GlobalTheory.T.polynomial_datum_action_of_pair hKP.base F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hp
  rw [eS]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    rw [eT]
    exact GlobalTheory.T.polynomial_theta_kernel_smooth F E σ hσ B a a' G X om om' hKP hT c hc hcc _ (hD _ g.2)
  · rintro β hβ _ ⟨g, rfl⟩
    obtain ⟨γ₀, hγ₀, hb⟩ := GlobalTheory.ThK.ZFinDerPol.line_back hσ hT.base.cm G.W hc β hβ
    obtain ⟨D, hD1, hD2⟩ := hP3 γ₀ hγ₀
    refine ⟨⟨D g.1, hD1 _ g.2⟩, ?_⟩
    have hder := GlobalTheory.T.theta_derivative_line_W F E σ B a a' G X om om' hKP hT γ₀ hγ₀ _ (hD _ g.2) _ (hD _ (hD1 _ g.2))
      (hasDerivAt_pure φ hSB hs ((hD2 _ g.2 _).2 rfl))
    rw [eT, eT]
    funext x
    have hb' : ∀ t, (toGAd hσ G.W.J hc).symm (β t) = γ₀ (Multiplicative.ofAdd t) := hb
    simp only [lineDer, map_mul, hb']
    exact (hder _).deriv.symm
  · rintro k hk _ ⟨g, rfl⟩
    obtain ⟨D, hD1, hD2⟩ := hP4 k hk
    refine ⟨⟨D g.1, hD1 _ g.2⟩, ?_⟩
    rw [eT, eT]
    funext x
    have e := acts_pure φ hSB hs ((hD2 _ g.2 _).2 rfl)
    simp only [map_mul, MulEquiv.symm_apply_apply]
    rw [← I_mul_right, e]
  · refine le_trans ?_ (GlobalTheory.T.polynomial_data_countable_rank hKP.base F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hp)
    exact rank_range_le T

end GlobalTheory.ThK.ZFinSmallStab

end
