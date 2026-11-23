import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataThetaLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDerivativeLineWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDerivativeLineVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralKInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivativeStatement

noncomputable section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.ThK.ThetaChain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem howe_chain {B : Base F E} (hKP : KP) {n d r s r' s' : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W}
    {χY χW : Chr F E} {o : Rep σ Y W} (h : IsPair B M χY χW o r s r' s') :
    ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ _), StrictMono N →
      (∀ i, GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o (N i)) → m ≤ L := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hY : Y.J.det ≠ 0 := fun h0 => RealUniq.det_ne_zero_of_sig (h.herm.sig w) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hW : W.J.det ≠ 0 := fun h0 => RealUniq.det_ne_zero_of_sig (h.skew.sig w) (by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])
  exact (hKP.howeDualityReal F E σ h.base.cm n d Y W M B.ψ χY χW o h.base.std h.herm.herm hY h.skew.skew hW h.resX h.resW
    h.hX h.hW h.weil B.emb h.herm.cartan h.skew.cartan).1

theorem I_mul {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (o : Rep σ Y W) (Φ : Fn F n d)
    (k h : UA σ W.J) : M.I o (o (1, k) Φ) h = M.I o Φ (h * k) := by
  simp only [Model.I, theta]
  congr 1
  funext g
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem strictMono_preimage {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ U)
    (T : P →ₗ[ℂ] V) {m : ℕ} (N : Fin m → Submodule ℂ V) (hN : StrictMono N) (hle : ∀ i, N i ≤ LinearMap.range T) :
    StrictMono fun i => ((N i).comap T).map P.subtype := by
  intro i j hij
  refine Submodule.map_strictMono_of_injective P.injective_subtype ?_
  have h := hN hij
  refine lt_of_le_of_ne (Submodule.comap_mono h.le) fun e => h.ne ?_
  rw [← Submodule.map_comap_eq_self (hle i), ← Submodule.map_comap_eq_self (hle j), e]

theorem chain_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c →
    ∀ (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GAd σ (c • G.W.J.map σ) → ℂ)), StrictMono N → (∀ i, N i ≤ (Submodule.span ℂ {ψ : GAd σ (c • G.W.J.map σ) → ℂ | ∃ f ∈ G.M'.Pol B.ψ B.emb,
        ψ = fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)})) →
        (∀ i β, IsRealLine σ (c • G.W.J.map σ) β → ∀ ψ ∈ N i, lineDer β ψ ∈ N i) →
        (∀ i, ∀ k ∈ KInf σ G.W B.emb, ∀ ψ ∈ N i, (fun x => ψ (x * toGAd hσ G.W.J hc k)) ∈ N i) → m ≤ L := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcσ φ hSB hev hv
  have hP := RealUniq.isPair_V' hT
  obtain ⟨hA1, hA2, hA3, hA4⟩ := GlobalTheory.T.polynomial_datum_action_of_pair hKP.base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP
  obtain ⟨L, hL⟩ := howe_chain hKP hP
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.pol_data_theta_linear F E σ B a a' G X om om' hKP hT
  have hs : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2
  have hD : ∀ f ∈ G.M'.Pol B.ψ B.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ := fun f hf =>
    ⟨Submodule.subset_span ⟨f, hf, φ, hSB, hev, rfl⟩, Submodule.subset_span ⟨f, φ, hSB, hev, hv, rfl⟩⟩
  obtain ⟨T, hTf⟩ : ∃ T : G.M'.Pol B.ψ B.emb →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ), ∀ f (hf : f ∈ G.M'.Pol B.ψ B.emb),
      T ⟨f, hf⟩ = fun x => G.M'.I om' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ((toGAd hσ G.W.J hc).symm x) :=
    ⟨LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ Λ ∘ₗ
      LinearMap.codRestrict _ (GlobalTheory.ThetaFacInf.pureL φ ∘ₗ (G.M'.Pol B.ψ B.emb).subtype) (fun f => hD f.1 f.2),
      fun f hf => funext fun x => congrFun (hΛ ⟨_, hD f hf⟩) _⟩
  refine ⟨L, fun m N hN hle hlie hcpt => hL m _ (strictMono_preimage _ T N hN fun i => (hle i).trans ?_) fun i => ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, hTf f hf⟩
  have mk : ∀ f (hf : f ∈ G.M'.Pol B.ψ B.emb), T ⟨f, hf⟩ ∈ N i →
      f ∈ ((N i).comap T).map (G.M'.Pol B.ψ B.emb).subtype := fun f hf h => ⟨⟨f, hf⟩, h, rfl⟩
  refine ⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ h
    obtain ⟨D, hDm, hDi⟩ := hA1 γ hγ
    have h₁ : f₁ ∈ G.M'.Pol B.ψ B.emb := (hDi f hf f₁).1 h ▸ hDm f hf
    refine mk f₁ h₁ ?_
    rw [hTf, GlobalTheory.T.theta_derivative_line_V F E σ B a a' G X om om' hKP hT γ hγ _ (hD f hf) _ (hD f₁ h₁)
      (GlobalTheory.ThetaFacInf.Fib.hasDerivAt_pure φ hSB hs h)]
    exact (N i).zero_mem
  · intro k hk f hf f₁ h
    obtain ⟨D, hDm, hDi⟩ := hA2 k hk
    have h₁ : f₁ ∈ G.M'.Pol B.ψ B.emb := (hDi f hf f₁).1 h ▸ hDm f hf
    refine mk _ (Submodule.sub_mem _ h₁ hf) ?_
    have e : T ⟨f₁, h₁⟩ = T ⟨f, hf⟩ := by
      rw [hTf, hTf, ← GlobalTheory.ThetaFacInf.Fib.acts_pure φ hSB hs h,
        GlobalTheory.T.theta_integral_K_invariant F E σ B a a' G X om om' hKP hT k hk _ (hD f hf)]
    have e2 : T ⟨f₁ - f, Submodule.sub_mem _ h₁ hf⟩ = T ⟨f₁, h₁⟩ - T ⟨f, hf⟩ := by
      rw [← LinearMap.map_sub]; rfl
    rw [e2, e, sub_self]
    exact (N i).zero_mem
  · rintro γ hγ _ ⟨⟨f, hf⟩, hfN, rfl⟩ f₁ h
    obtain ⟨D, hDm, hDi⟩ := hA3 γ hγ
    have h₁ : f₁ ∈ G.M'.Pol B.ψ B.emb := (hDi f hf f₁).1 h ▸ hDm f hf
    refine mk f₁ h₁ ?_
    obtain ⟨r, β, hβ, hder⟩ := GlobalTheory.T.line_to_GAd_derivative F E σ hσ hT.base.cm _ G.W c hc γ hγ
    have hfN' : T ⟨f, hf⟩ ∈ N i := hfN
    have e : T ⟨f₁, h₁⟩ = ∑ j, lineDer (β j) (T ⟨f, hf⟩) := by
      funext g
      have d1 := hder _ (GlobalTheory.T.polynomial_theta_kernel_smooth F E σ hσ B a a' G X om om' hKP hT c hc hcσ _ (hD f hf)) g
      have d2 := GlobalTheory.T.theta_derivative_line_W F E σ B a a' G X om om' hKP hT γ hγ _ (hD f hf) _ (hD f₁ h₁)
        (GlobalTheory.ThetaFacInf.Fib.hasDerivAt_pure φ hSB hs h) ((toGAd hσ G.W.J hc).symm g)
      simp only [map_mul, MulEquiv.symm_apply_apply] at d1
      rw [hTf, hTf, Finset.sum_apply]
      exact d2.unique d1
    rw [e]
    exact Submodule.sum_mem _ fun j _ => hlie i _ (hβ j) _ hfN'
  · rintro k hk _ ⟨⟨f, hf⟩, hfN, rfl⟩ f₁ h
    obtain ⟨D, hDm, hDi⟩ := hA4 k hk
    have h₁ : f₁ ∈ G.M'.Pol B.ψ B.emb := (hDi f hf f₁).1 h ▸ hDm f hf
    refine mk f₁ h₁ ?_
    have hfN' : T ⟨f, hf⟩ ∈ N i := hfN
    have e : T ⟨f₁, h₁⟩ = fun x => T ⟨f, hf⟩ (x * toGAd hσ G.W.J hc k) := by
      funext x
      rw [hTf, hTf, ← GlobalTheory.ThetaFacInf.Fib.acts_pure φ hSB hs h]
      simp only [map_mul, MulEquiv.symm_apply_apply]
      exact I_mul _ _ _ _ _
    rw [e]
    exact hcpt i k hk _ hfN'

end GlobalTheory.ThK.ThetaChain

end
