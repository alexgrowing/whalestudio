import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement

noncomputable section

namespace GlobalTheory.ThetaFacInf.Fib

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F]

theorem rest_finPart {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  have hz0 : ∀ v i, evFin F v (z i) = 0 := fun v i => by
    have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
    have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
    rw [one_mul] at h2
    rw [evFin, AlgHom.comp_apply]
    convert map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
    exact h2
  simp only [Pi.add_apply, map_add, hz0, add_zero]

theorem hasDerivAt_pure {κ : Type} [Fintype κ] {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h : ActsD (evI F) T f f₁) :
    ∀ x, HasDerivAt (fun t => T t (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ x) 0 :=
  h _ (rest_finPart f φ hSB hstd)

theorem acts_pure {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h : Acts (evI F) T f f₁) : T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ :=
  h _ (rest_finPart f φ hSB hstd)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem thetaSubInf_fib (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hP1 : ∀ γ ∈ Lines σ Y, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hP2 : ∀ k ∈ KInf σ Y B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol B.ψ B.emb)
    (hP3 : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁)
    (hP4 : ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁)
    (N : Submodule ℂ (Fn F n d)) (hN : GlobalTheory.ThetaFac.IsMaxTh B om (PolData B M) N)
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hev : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (M.Pol B.ψ B.emb ⊓ N.comap (GlobalTheory.ThetaFacInf.pureL φ)) := by
  have hs : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hev.and hstd).mono fun v hv => hv.1.trans hv.2
  have hD : ∀ f ∈ M.Pol B.ψ B.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ PolData B M := fun f hf =>
    Submodule.subset_span ⟨f, hf, φ, hSB, hev, rfl⟩
  refine ⟨inf_le_left, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ h
    have h₁ := hP1 γ hγ f hf f₁ h
    refine ⟨h₁, ?_⟩
    show GlobalTheory.ThetaFacInf.pureL φ f₁ ∈ N
    rw [GlobalTheory.ThetaFacInf.pureL_apply]
    exact hN.coinv.lie γ hγ _ (hD f hf) _ (hD f₁ h₁) (hasDerivAt_pure φ hSB hs h)
  · intro k hk f hf f₁ h
    have h₁ := hP2 k hk f hf f₁ h
    refine ⟨Submodule.sub_mem _ h₁ hf, ?_⟩
    show GlobalTheory.ThetaFacInf.pureL φ (f₁ - f) ∈ N
    rw [map_sub, GlobalTheory.ThetaFacInf.pureL_apply, GlobalTheory.ThetaFacInf.pureL_apply, ← acts_pure φ hSB hs h]
    exact hN.coinv.cpt k hk _ (hD f hf)
  · intro γ hγ f hf f₁ h
    obtain ⟨f₂, hf₂, -, huniq⟩ := hP3 γ hγ f hf.1
    have e := huniq f₁ h
    subst e
    refine ⟨hf₂, ?_⟩
    show GlobalTheory.ThetaFacInf.pureL φ f₁ ∈ N
    rw [GlobalTheory.ThetaFacInf.pureL_apply]
    have hfN : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N := hf.2
    exact hN.stab.lie γ hγ _ hfN _ (hD f₁ hf₂) (hasDerivAt_pure φ hSB hs h)
  · intro k hk f hf f₁ h
    obtain ⟨f₂, hf₂, -, huniq⟩ := hP4 k hk f hf.1
    have e := huniq f₁ h
    subst e
    refine ⟨hf₂, ?_⟩
    show GlobalTheory.ThetaFacInf.pureL φ f₁ ∈ N
    rw [GlobalTheory.ThetaFacInf.pureL_apply, ← acts_pure φ hSB hs h]
    have hfN : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N := hf.2
    exact hN.stab.cpt k hk _ hfN

end GlobalTheory.ThetaFacInf.Fib

end

namespace GlobalTheory.ThetaFacInf.Fib

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

theorem thetaSubInf_pol_comap : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N,
    GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → ∀ (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
    GlobalTheory.Published.ThetaSubInf G.M B.ψ B.emb om (G.M.Pol B.ψ B.emb ⊓ N.comap (GlobalTheory.ThetaFacInf.pureL φ)) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN φ hSB hev
  obtain ⟨hP1, hP2, hP3, hP4⟩ := GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hM.triple
  exact thetaSubInf_fib B G.M om hM.triple.geo.hM.std hP1 hP2 hP3 hP4 N hN φ hSB hev

end GlobalTheory.ThetaFacInf.Fib
