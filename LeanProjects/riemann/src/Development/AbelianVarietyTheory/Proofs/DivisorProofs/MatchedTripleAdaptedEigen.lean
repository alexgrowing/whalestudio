import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUpdate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultilinearFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearQuotientFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMultilinearVacuumOutside
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableComplementInSocle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxThetaVanishingArchimedean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationCmExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaExistsDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPolynomialLinesInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaLiftCuspIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLowPartIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDataLocalIdentityRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDataLocalIdentityFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerMemSpanStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Matrix

namespace GlobalTheory.ThetaFacIrrSmall

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section General

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro h0
  obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hy' : star y ≠ 0 := by simpa using hy
  have := h.2.2 (star y) hy'
  rw [star_star, hMy, dotProduct_zero] at this
  simp at this

theorem det_ne_zero_of_triple {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') : G.V'.J.det ≠ 0 ∧ G.W.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  constructor
  · have h1 := det_ne_zero_of_isCartan (h.geo.hV'.cartan w)
    intro h0
    apply h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · have h1 := det_ne_zero_of_isCartan (h.geo.hW.cartan w)
    intro h0
    apply h1
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]

theorem actsD_zero {κ : Type} [Fintype κ] (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have h0 : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero]
  simpa using hasDerivAt_const (0:ℝ) (0:ℂ)

theorem acts_zero {κ : Type} [Fintype κ] (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have h0 : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by
    funext y; simp [tens]
  rw [h0, map_zero]

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

variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

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
    (N : Submodule ℂ (Fn F n d)) (hN : GlobalTheory.ThetaFac.IsMaxTh B om (PolData B M ⊓ M.So B.ψ B.τ₁) N)
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hev : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) (h1 : φ B.v₁ ∈ Submodule.span ℂ (M.SoLoc B.ψ B.τ₁)) :
    GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om (M.Pol B.ψ B.emb ⊓ N.comap (GlobalTheory.ThetaFacInf.pureL φ)) := by
  have hs : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hev.and hstd).mono fun v hv => hv.1.trans hv.2
  have hD : ∀ f ∈ M.Pol B.ψ B.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ PolData B M ⊓ M.So B.ψ B.τ₁ := fun f hf =>
    GlobalTheory.SoPure.pure_mem_polSo B M hstd f hf φ hSB hev h1
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

end General

theorem kerSub : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → GlobalTheory.Published.ThetaSubInf G.M' B.ψ B.emb om' (G.M'.Pol B.ψ B.emb ⊓ LinearMap.ker R.p') := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  obtain ⟨hP1, hP2, hP3, hP4⟩ := GlobalTheory.T.theta_polynomial_lines_invariance hKP F E σ B a a' G X om om' hM.triple
  refine ⟨inf_le_left, ?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ hA
    exact ⟨hP1 γ hγ f hf f₁ hA, hM.real.quot'.lie γ hγ f hf f₁ hA⟩
  · intro k hk f hf f₁ hA
    refine ⟨sub_mem (hP2 k hk f hf f₁ hA) hf, ?_⟩
    show R.p' (f₁ - f) = 0
    rw [map_sub, hM.real.quot'.cpt k hk f hf f₁ hA, sub_self]
  · intro γ hγ f hf f₁ hA
    obtain ⟨g, hg, _, hu⟩ := hP3 γ hγ f hf.1
    refine ⟨hu f₁ hA ▸ hg, ?_⟩
    show R.p' f₁ = 0
    have hf0 : R.p' f = 0 := hf.2
    have := hM.real.lie γ hγ 0 (zero_mem _) f hf.1 0 f₁
      (actsD_zero (fun t => om (1, γ (Multiplicative.ofAdd t)))) hA (by rw [hf0, map_zero])
    rw [← this, map_zero]
  · intro k hk f hf f₁ hA
    obtain ⟨g, hg, _, hu⟩ := hP4 k hk f hf.1
    refine ⟨hu f₁ hA ▸ hg, ?_⟩
    show R.p' f₁ = 0
    have hf0 : R.p' f = 0 := hf.2
    have := hM.real.cpt k hk 0 (zero_mem _) f hf.1 0 f₁ (acts_zero (om (1, k))) hA (by rw [hf0, map_zero])
    rw [← this, map_zero]

theorem ker_ne {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'}
    (hR : IsRealMaps B G om om' R) : G.M'.Pol B.ψ B.emb ⊓ LinearMap.ker R.p' ≠ G.M'.Pol B.ψ B.emb := by
  intro h
  have hn := hR.nontriv
  have h0 : (G.M'.Pol B.ψ B.emb).map R.p' = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨f, hf, rfl⟩
    rw [← h] at hf
    exact (Submodule.mem_bot ℂ).2 hf.2
  exact bot_ne_top (h0.symm.trans hR.quot'.onto)

theorem le_ker_of_ne : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ P : Submodule ℂ (SInf F (Fin a' × Fin (a + a'))),
    GlobalTheory.Published.ThetaSubInf G.M' B.ψ B.emb om' P → P ≠ G.M'.Pol B.ψ B.emb → P ≤ LinearMap.ker R.p' := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM P hP hne
  have hKr := kerSub hKP F E σ B a a' G X om om' R Rf hM
  have hT := hM.triple
  obtain ⟨-, -, hstW, hstK⟩ := GlobalTheory.T.theta_polynomial_lines_invariance hKP F E σ B a a' G X om om' hT
  obtain ⟨hdV, hdW⟩ := det_ne_zero_of_triple hT
  have hp := GlobalTheory.ThK.Inhab.pairV' hT
  have hHowe := (hKP.howeDualityReal F E σ hT.base.cm a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' hT.base.std
    hT.geo.hV'.herm hdV hT.geo.hW.skew hdW hp.resX hp.resW hp.hX hp.hW hT.weil' B.emb hT.geo.hV'.cartan
    hT.geo.hW.cartan).2 P _ hP hKr hne (ker_ne hM.real)
  rcases hM.real.irred (P.map R.p') (by
      rintro γ hγ f hf f₁ hd ⟨g, hg, hpg⟩
      obtain ⟨g₁, -, hgd, -⟩ := hstW γ hγ g (hP.1 hg)
      exact ⟨g₁, hP.2.2.2.1 γ hγ g hg g₁ hgd, (hM.real.lie γ hγ f hf g (hP.1 hg) f₁ g₁ hd hgd hpg.symm).symm⟩) (by
      rintro k hk f hf f₁ hd ⟨g, hg, hpg⟩
      obtain ⟨g₁, -, hgd, -⟩ := hstK k hk g (hP.1 hg)
      exact ⟨g₁, hP.2.2.2.2 k hk g hg g₁ hgd, (hM.real.cpt k hk f hf g (hP.1 hg) f₁ g₁ hd hgd hpg.symm).symm⟩) with h | h
  · intro x hx
    have : R.p' x ∈ P.map R.p' := Submodule.mem_map_of_mem hx
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · exfalso
    apply hHowe
    refine le_antisymm (sup_le hP.1 inf_le_left) fun f hf => ?_
    obtain ⟨g, hg, hpg⟩ : R.p' f ∈ P.map R.p' := h ▸ Submodule.mem_top
    have hfg : f = g + (f - g) := by abel
    rw [hfg]
    exact Submodule.add_mem_sup hg
      (Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hf (hP.1 hg), LinearMap.mem_ker.2 (by rw [map_sub, hpg, sub_self])⟩)

theorem killInf : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), f ∈ G.M'.Pol B.ψ B.emb → (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) → R.p' f = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN f φ hf hφ hφc h1 hp
  obtain ⟨hP1, hP2, hP3, hP4⟩ := GlobalTheory.T.theta_polynomial_lines_invariance hKP F E σ B a a' G X om om' hM.triple
  have hfK : f ∈ G.M'.Pol B.ψ B.emb ⊓ LinearMap.ker R.p' := Submodule.mem_inf.2 ⟨hf, LinearMap.mem_ker.2 hp⟩
  have key : f ∈ N.comap (GlobalTheory.ThetaFacInf.pureL φ) := by
    by_cases hF : G.M'.Pol B.ψ B.emb ⊓ N.comap (GlobalTheory.ThetaFacInf.pureL φ) = G.M'.Pol B.ψ B.emb
    · have : f ∈ G.M'.Pol B.ψ B.emb ⊓ N.comap (GlobalTheory.ThetaFacInf.pureL φ) := by rw [hF]; exact hf
      exact (Submodule.mem_inf.1 this).2
    · exact GlobalTheory.T.matched_theta_lift_cusp_integral hKP F E σ B a a' G X om om' R Rf hM N hN φ hφ hφc h1 _
        (kerSub hKP F E σ B a a' G X om om' R Rf hM)
        (le_inf inf_le_left (le_ker_of_ne hKP F E σ B a a' G X om om' R Rf hM _
          (thetaSubInf_fib B G.M' om' hM.triple.geo.hM'.std hP1 hP2 hP3 hP4 N hN φ hφ hφc h1) hF)) (ker_ne hM.real) hfK
  exact key

theorem stableComplementAt : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → (∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), G.M'.I om' Ψ = 0 → Ψ ∈ N) → ∀ (v : Pl F) (P : Submodule ℂ (Fn F a' (a + a'))), N ≤ P → P ≤ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) → (∀ h ∈ UAt σ G.W (evFin F v), ∀ Φ ∈ P, om' (1, h) Φ ∈ P) → ∃ C : Submodule ℂ (Fn F a' (a + a')), C ≤ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧ (∀ h ∈ UAt σ G.W (evFin F v), ∀ Φ ∈ C, om' (1, h) Φ ∈ C) ∧ P ⊔ C = (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ∧ P ⊓ C = N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN hker v P hNP hPD hP
  have hcpt : ∀ k ∈ KInf σ G.W B.emb, ∀ Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om' v) N (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁),
      om' (1, k) Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om' v) N (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) := by
    intro k hk Φ hΦ
    have hk' := GlobalTheory.ThetaFacCompl.inv_mem_KInf B.emb hk
    have hfD := (GlobalTheory.T.matched_pair_theta_exists_data hKP F E σ B a a' G X om om' R Rf hM).2 k hk
    have hfg : om' (1, k) * om' (1, k⁻¹) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel, ← Prod.one_eq_mk, map_one]
    have hgf : om' (1, k⁻¹) * om' (1, k) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, inv_mul_cancel, ← Prod.one_eq_mk, map_one]
    have comm : ∀ k₀ ∈ KInf σ G.W B.emb, ∀ t ∈ GlobalTheory.ThKLocSS.opsAt om' v, t * om' (1, k₀) = om' (1, k₀) * t := by
      rintro k₀ hk₀ _ ⟨h₀, hh₀, rfl⟩
      rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one,
        GlobalTheory.ThKLocSS.commute_of_evI_evFin v hk₀.1 hh₀]
    have hfN : N.map (om' (1, k)) ≤ N := Submodule.map_le_iff_le_comap.2 fun x hx => hN.stab.cpt k hk x hx
    have hgN : N.map (om' (1, k⁻¹)) ≤ N := Submodule.map_le_iff_le_comap.2 fun x hx => hN.stab.cpt k⁻¹ hk' x hx
    have hle : GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om' v) N (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) ≤
        (GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om' v) N (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)).comap (om' (1, k)) := by
      refine sup_le (fun x hx => GlobalTheory.ThKLocSS.le_socleOver _ N _ (hfN ⟨x, hx, rfl⟩)) (sSup_le ?_)
      rintro S ⟨hSD, hS⟩
      refine Submodule.map_le_iff_le_comap.1 (GlobalTheory.ThKLocSS.le_socleOver_of_simple _ ?_ ?_)
      · rintro _ ⟨x, hx, rfl⟩; exact hfD x (hSD hx)
      · exact GlobalTheory.ThKLocSS.isSimpleOver_map _ _ hfg hgf hfN hgN (comm k hk) (comm k⁻¹ hk') hS
    exact hle hΦ
  have hWS : GlobalTheory.ThetaFac.WStable B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) (GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om' v) N (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) :=
    ⟨GlobalTheory.T.matched_data_local_identity_real hKP F E σ B a a' G X om om' R Rf hM N hN v, GlobalTheory.T.matched_data_local_identity_finite hKP F E σ B a a' G X om om' R Rf hM N hN v, hcpt⟩
  obtain ⟨S, hSD, hS⟩ := GlobalTheory.T.matched_triple_lowPart_identity hKP F E σ B a a' G X om om' R Rf hM N hN hker v
  set D := (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) with hD
  set T := GlobalTheory.ThKLocSS.opsAt om' v with hTdef
  have hND : N ≤ D := hN.le
  have hsoc : GlobalTheory.ThKLocSS.socleOver T N D = D := by
    rcases hN.max _ (GlobalTheory.ThKLocSS.le_socleOver T N D) (GlobalTheory.ThKLocSS.socleOver_le T hND) hWS with h | h
    · exfalso
      have := GlobalTheory.ThKLocSS.le_socleOver_of_simple T hSD hS
      rw [h] at this
      exact lt_irrefl _ (lt_of_lt_of_le hS.1 this)
    · exact h
  have hNs : GlobalTheory.ThKLocSS.OpStable T N := (GlobalTheory.ThKLocSS.opStable_opsAt_iff om' v N).2 (hN.stab.fin v)
  have hPs : GlobalTheory.ThKLocSS.OpStable T P := (GlobalTheory.ThKLocSS.opStable_opsAt_iff om' v P).2 hP
  obtain ⟨C, hCD, hCs, hsup, hinf⟩ :=
    GlobalTheory.ThKLocSS.exists_opStable_compl_of_socleOver_eq _ T N D P hND hNs hsoc hNP hPD hPs
  exact ⟨C, hCD, (GlobalTheory.ThKLocSS.opStable_opsAt_iff om' v C).1 hCs, hsup, hinf⟩

theorem radZero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → (∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), G.M'.I om' Ψ = 0 → Ψ ∈ N) → ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), f ∈ G.M'.Pol B.ψ B.emb → (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∉ N → ∀ v : Pl F, v ≠ B.v₁ → ∃ P : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ), Maximal (fun Q => GlobalTheory.Published.ThetaSub om' v Q ∧ Q ≠ SB _) P ∧ φ v ∉ P := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN hI f φ hf hφ hφc hφ1 hn v hv1
  have hT := hM.triple
  classical
  have hP := GlobalTheory.ThK.Inhab.pairV' hT
  have hA := GlobalTheory.T.theta_action_exists hKP.base
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    (hφc.and hP.good.std).mono fun w hw => hw.1.trans hw.2
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  let lin : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] Fn F a' (a + a') :=
    { toFun := fun χ => tens (evFin F v) χ ρ
      map_add' := fun χ χ' => by funext x; simp [tens, add_mul]
      map_smul' := fun c χ => by funext x; simp [tens, mul_assoc] }
  have hlin : ∀ χ, lin χ = pure f (Function.update φ v χ) := fun χ => hρt χ
  have hupd : ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ w, Function.update φ v χ w ∈ SB _ := by
    intro χ hχ w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hχ
    · rw [Function.update_of_ne hw]; exact hφ w
  have hD : ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), lin χ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ := by
    intro χ hχ
    rw [hlin]
    refine GlobalTheory.SoPure.pure_mem_polSo B G.M' hP.good.std f hf _ (hupd χ hχ) ?_ (by rw [Function.update_of_ne hv1.symm]; exact hφ1)
    filter_upwards [hφc, Filter.eventually_cofinite_ne v] with w hw hne
    rw [Function.update_of_ne hne]; exact hw
  have hRest : ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rest (evFin F v) χ ρ := fun χ hχ =>
    ⟨hρ, by rw [hρt]; exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd χ hχ) (GlobalTheory.PureFactor.update_eventually φ v χ hstd)⟩
  have h1V : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.V'.J) - 1) = 0
    have : mat (1 : UA σ G.V'.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  have hex : ∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ χ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) χ χ₁ := by
    intro h hh χ hχ
    obtain ⟨χ₁, ⟨h1, h2⟩, -⟩ := (hA F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP v).1 1 h1V h hh χ hχ
    exact ⟨χ₁, h1, h2⟩
  have hact : ∀ g, ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ χ₁, Acts (evFin F v) (om' g) χ χ₁ →
      om' g (lin χ) = lin χ₁ := fun g χ hχ χ₁ hA => hA ρ (hRest χ hχ)

  set D := PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ with hDdef
  set SBv := SB (Fin a' × Fin (a + a') → Fv F v) with hSBv
  let St : Submodule ℂ (Fn F a' (a + a')) → Prop :=
    fun P => ∀ h ∈ UAt σ G.W (evFin F v), ∀ Φ ∈ P, om' (1, h) Φ ∈ P
  have hStN : St N := fun h hh Φ hΦ => hN.stab.fin v h hh Φ hΦ
  set M := N ⊔ SBv.map lin with hMdef
  have hMD : M ≤ D := sup_le hN.le (by rintro _ ⟨χ, hχ, rfl⟩; exact hD χ hχ)

  have hStImg : ∀ Q : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ), Q ≤ SBv →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ Q, ∀ χ₁ ∈ SBv, Acts (evFin F v) (om' (1, h)) χ χ₁ → χ₁ ∈ Q) →
      St (N ⊔ Q.map lin) := by
    intro Q hQ hQs h hh Φ hΦ
    obtain ⟨n, hn, y, ⟨χ, hχ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hΦ
    obtain ⟨χ₁, hχ₁, hA₁⟩ := hex h hh χ (hQ hχ)
    rw [map_add, hact _ χ (hQ hχ) χ₁ hA₁]
    exact Submodule.add_mem_sup (hStN h hh n hn) ⟨χ₁, hQs h hh χ hχ χ₁ hχ₁ hA₁, rfl⟩
  have hStM : St M := hStImg SBv le_rfl (fun _ _ _ _ χ₁ hχ₁ _ => hχ₁)
  have hx : pure f φ ∈ M := by
    have e : lin (φ v) = pure f φ := by rw [hlin, Function.update_eq_self]
    rw [← e]
    exact Submodule.mem_sup_right ⟨φ v, hφ v, rfl⟩
  obtain ⟨Ph, hPhSt, hNPh, hPhM, hxPh, hPhmax⟩ := GlobalTheory.ThetaFacW.exists_max_not_mem St M N hStN le_sup_left
    (fun c hne hc hcs h hh Φ hΦ => by
      obtain ⟨P, hP, hΦP⟩ := (Submodule.mem_sSup_of_directed hne hc.directedOn).1 hΦ
      exact (Submodule.mem_sSup_of_directed hne hc.directedOn).2 ⟨P, hP, hcs P hP h hh Φ hΦP⟩)
    (fun N₁ N₂ h₁ h₂ _ _ h hh Φ hΦ => by
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
      rw [map_add]; exact Submodule.add_mem_sup (h₁ h hh y hy) (h₂ h hh z hz))
    (fun P hPSt hNP hPM => by
      obtain ⟨C, hCD, hCSt, hsup, hinf⟩ := stableComplementAt hKP F E σ B a a' G X om om' R Rf hM N hN hI v P hNP (hPM.trans hMD) hPSt
      refine ⟨C ⊓ M, fun h hh Φ hΦ => ⟨hCSt h hh Φ hΦ.1, hStM h hh Φ hΦ.2⟩, inf_le_right, ?_, ?_⟩
      · rw [← sup_inf_assoc_of_le C hPM, hsup]; exact inf_eq_right.2 hMD
      · rw [← inf_assoc, hinf]; exact inf_eq_left.2 le_sup_left)
    (pure f φ) hx hn

  set Pl := Ph.comap lin ⊓ SBv with hPl
  have hmemM : ∀ m ∈ M, ∃ n ∈ N, ∃ χ ∈ SBv, m = n + lin χ := by
    intro m hm
    obtain ⟨n, hn, y, ⟨χ, hχ, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hm
    exact ⟨n, hn, χ, hχ, rfl⟩
  have hPlSub : GlobalTheory.Published.ThetaSub om' v Pl := by
    refine ⟨?_, inf_le_right, ?_⟩
    · rw [augAt, Submodule.span_le]
      rintro _ ⟨g, hg, χ, hχ, χ₁, hχ₁, hA₁, rfl⟩
      refine ⟨?_, Submodule.sub_mem _ hχ₁ hχ⟩
      show lin (χ₁ - χ) ∈ Ph
      rw [map_sub, ← hact _ χ hχ χ₁ hA₁]
      exact hNPh (hN.coinv.fin v g hg _ (hD χ hχ))
    · intro h hh χ hχ χ₁ hχ₁ hA₁
      refine ⟨?_, hχ₁⟩
      show lin χ₁ ∈ Ph
      rw [← hact _ χ hχ.2 χ₁ hA₁]
      exact hPhSt h hh _ hχ.1
  have hvPl : φ v ∉ Pl := fun h => hxPh (by
    have := h.1
    simpa [Submodule.mem_comap, hlin, Function.update_eq_self] using this)
  refine ⟨Pl, ⟨⟨hPlSub, fun e => hvPl (e ▸ hφ v)⟩, ?_⟩, hvPl⟩
  rintro Q ⟨hQ, hQne⟩ hPlQ
  have hQSB : Q ≤ SBv := hQ.2.1
  have hStQ := hStImg Q hQSB (fun h hh χ hχ χ₁ hχ₁ hA₁ => hQ.2.2 h hh χ hχ χ₁ hχ₁ hA₁)
  have hQM : N ⊔ Q.map lin ≤ M := sup_le_sup_left (Submodule.map_mono hQSB) _
  have hPhQ : Ph ≤ N ⊔ Q.map lin := by
    intro m hm
    obtain ⟨n, hn, χ, hχ, rfl⟩ := hmemM m (hPhM hm)
    have hχP : χ ∈ Pl := ⟨by
      show lin χ ∈ Ph
      have := Ph.sub_mem hm (hNPh hn)
      simpa using this, hχ⟩
    exact Submodule.add_mem_sup hn ⟨χ, hPlQ hχP, rfl⟩
  rcases hPhmax _ hPhQ hQM hStQ with e | e
  · intro χ hχ
    refine ⟨?_, hQSB hχ⟩
    show lin χ ∈ Ph
    rw [← e]; exact Submodule.mem_sup_right ⟨χ, hχ, rfl⟩
  · exfalso
    refine hQne (le_antisymm hQSB fun χ hχ => ?_)
    have hm : lin χ ∈ N ⊔ Q.map lin := e ▸ Submodule.mem_sup_right ⟨χ, hχ, rfl⟩
    obtain ⟨n, hn, y, ⟨χ', hχ', rfl⟩, hsum⟩ := Submodule.mem_sup.1 hm
    have hd : χ - χ' ∈ Pl := by
      refine ⟨?_, Submodule.sub_mem _ hχ (hQSB hχ')⟩
      show lin (χ - χ') ∈ Ph
      rw [map_sub, ← hsum, add_sub_cancel_right]
      exact hNPh hn
    simpa using Q.add_mem (hPlQ hd) hχ'

theorem one_mem_UAt {n : ℕ} (Y : Spc F E n) (v : Pl F) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := by
  intro u _
  show u • (mat (1 : UA σ Y.J) - 1) = 0
  have : mat (1 : UA σ Y.J) = 1 := rfl
  rw [this, sub_self, smul_zero]

theorem ker_maximal (hKP : GlobalTheory.ThK.KP) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} {Rf : FinMaps F a a'} (hT : IsTriple B G X om om') (hf : IsFinMaps B G X om om' Rf) (v : Pl F) :
    Maximal (fun Q => GlobalTheory.Published.ThetaSub om' v Q ∧ Q ≠ SB _) (LinearMap.ker (Rf.p' v) ⊓ SB _) := by
  have hsub : GlobalTheory.Published.ThetaSub om' v (LinearMap.ker (Rf.p' v) ⊓ SB _) := by
    refine ⟨le_inf (hf.inv' v) ?_, inf_le_right, ?_⟩
    · rw [augAt, Submodule.span_le]
      rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
      exact Submodule.sub_mem _ hφ₁ hφ
    · intro h hh φ hφ φ₁ hφ₁ hA
      obtain ⟨hφk, hφs⟩ := Submodule.mem_inf.1 hφ
      refine Submodule.mem_inf.2 ⟨?_, hφ₁⟩
      have h0 : Acts (evFin F v) (om (1, h)) (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) 0 := by
        intro r _
        have e : tens (evFin F v) (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
          funext x; simp [tens]
        rw [e, map_zero]
      have := hf.equiv v h hh 0 (Submodule.zero_mem _) φ hφs 0 (Submodule.zero_mem _) φ₁ hφ₁ h0 hA
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hφk).symm)
      rw [LinearMap.mem_ker, ← this, map_zero]
  refine ⟨⟨hsub, fun hK => ?_⟩, fun P hP hKP' => ?_⟩
  · haveI := hf.nontriv v
    obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
    have hy' : y ∈ (SB _).map (Rf.p' v) := by rw [hf.onto' v]; trivial
    obtain ⟨φ, hφ, rfl⟩ := hy'
    have : φ ∈ LinearMap.ker (Rf.p' v) ⊓ SB _ := by rw [hK]; exact hφ
    exact hy (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).1)
  · obtain ⟨hP, hPne⟩ := hP
    have key : ∀ φ ∈ SB _, Rf.p' v φ ∈ P.map (Rf.p' v) → φ ∈ P := by
      intro φ hφ hm
      obtain ⟨ψ, hψ, he⟩ := hm
      have hd : φ - ψ ∈ LinearMap.ker (Rf.p' v) ⊓ SB _ :=
        Submodule.mem_inf.2 ⟨by rw [LinearMap.mem_ker, map_sub, he, sub_self],
          Submodule.sub_mem _ hφ (hP.2.1 hψ)⟩
      simpa using P.add_mem (hKP' hd) hψ
    rcases hf.irred v (P.map (Rf.p' v)) (by
        rintro h hh φ hφ φ₁ hφ₁ hA ⟨χ, hχ, he⟩
        obtain ⟨χ₁, ⟨h1, h2⟩, -⟩ := (GlobalTheory.T.theta_action_exists hKP.base F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _
          (GlobalTheory.ThK.Inhab.pairV' hT) v).1 1 (one_mem_UAt _ v) h hh χ (hP.2.1 hχ)
        exact ⟨χ₁, hP.2.2 h hh χ hχ χ₁ h1 h2,
          (hf.equiv v h hh φ hφ χ (hP.2.1 hχ) φ₁ hφ₁ χ₁ h1 hA h2 he.symm).symm⟩) with h0 | h1
    · intro φ hφ
      refine Submodule.mem_inf.2 ⟨?_, hP.2.1 hφ⟩
      have : Rf.p' v φ ∈ P.map (Rf.p' v) := ⟨φ, hφ, rfl⟩
      rw [h0] at this
      exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 this)
    · exact absurd (le_antisymm hP.2.1 fun φ hφ => key φ hφ (by rw [h1]; trivial)) hPne

theorem killFin : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → (∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), G.M'.I om' Ψ = 0 → Ψ ∈ N) → ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), f ∈ G.M'.Pol B.ψ B.emb → (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) → ∀ v, v ≠ B.v₁ → Rf.p' v (φ v) = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN hI f φ hf hφ hφc h1 v hv1 hv
  by_contra hn
  have hT := hM.triple
  obtain ⟨P, hPm, hPv⟩ := radZero hKP F E σ B a a' G X om om' R Rf hM N hN hI f φ hf hφ hφc h1 hn v hv1
  obtain ⟨hdV, hdW⟩ := det_ne_zero_of_triple hT
  have hp := GlobalTheory.ThK.Inhab.pairV' hT
  have e := GlobalTheory.T.weil_representation_cm_extension hKP.base hKP.howeDualityUnitary hKP.minguezThetaGL F E σ hT.base.cm a' (a + a') G.V' G.W G.M' B.ψ
    X.α (X.α / X.β) om' hT.base.std hT.geo.hV'.herm hdV hT.geo.hW.skew hdW hp.resX hp.resW hp.hX hp.hW hT.weil' v P _ hPm
    (ker_maximal hKP hT hM.fin v)
  rw [e] at hPv
  exact hPv (Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hv, hφ v⟩)

theorem killOne : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), f ∈ G.M'.Pol B.ψ B.emb → (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) → Rf.p' B.v₁ (φ B.v₁) = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN f φ hf hφ hφc h1 hv
  classical
  have hs := hM.triple.geo.hM'.std
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    (hφc.and hs).mono fun w hw => hw.1.trans hw.2
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor B.v₁ f φ hstd
  obtain ⟨L, hL⟩ := GlobalTheory.SoPure.exists_linear_update B.v₁ f φ hstd
  have hupd : ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ w, Function.update φ B.v₁ χ w ∈ SB _ := by
    intro χ hχ w
    by_cases hw : w = B.v₁
    · subst hw; rw [Function.update_self]; exact hχ
    · rw [Function.update_of_ne hw]; exact hφ w
  have hm := GlobalTheory.T.matched_data_local_identity_alt hKP F E σ B a a' G X om om' R Rf hM _ h1 hv
  have hN' : φ B.v₁ ∈ N.comap L := by
    refine (Submodule.span_le (p := N.comap L)).2 ?_ hm
    rintro _ ⟨g, hg, χ, hχ, χ₁, hχ₁, hA, rfl⟩
    have hR : Rest (evFin F B.v₁) χ ρ := ⟨hρ, by
      rw [hρt]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd χ hχ.1) (GlobalTheory.PureFactor.update_eventually φ B.v₁ χ hstd)⟩
    have hact := hA ρ hR
    rw [hρt, hρt] at hact
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, hL, hL, ← hact]
    refine hN.coinv.fin B.v₁ g hg _ (GlobalTheory.SoPure.pure_mem_polSo B G.M' hs f hf _ (hupd χ hχ.1) ?_
      (by rw [Function.update_self]; exact Submodule.subset_span hχ))
    filter_upwards [hφc, Filter.eventually_cofinite_ne B.v₁] with w hw hne
    rw [Function.update_of_ne hne]; exact hw
  rwa [Submodule.mem_comap, hL, Function.update_eq_self] at hN'

theorem exists_proj {A P : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] (S : Submodule ℂ A)
    (p : A →ₗ[ℂ] P) (hp : ∀ ξ, ∃ x ∈ S, p x = ξ) :
    ∃ π : A →ₗ[ℂ] A, (∀ x, π x ∈ S) ∧ (∀ x ∈ S, π x = x) ∧ ∀ x, p (π x) = p x := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective S.subtype (Submodule.ker_subtype S)
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (p.comp S.subtype)
    (LinearMap.range_eq_top.2 fun ξ => by obtain ⟨x, hx, e⟩ := hp ξ; exact ⟨⟨x, hx⟩, e⟩)
  have hs' : ∀ ξ, p (s ξ : A) = ξ := fun ξ => LinearMap.congr_fun hs ξ
  have hr' : ∀ x ∈ S, (r x : A) = x := fun x hx => congrArg Subtype.val (LinearMap.congr_fun hr ⟨x, hx⟩)
  refine ⟨S.subtype.comp (r + s.comp (p - p.comp (S.subtype.comp r))), fun x => ((r + s.comp (p - p.comp (S.subtype.comp r))) x).2, fun x hx => ?_,
    fun x => ?_⟩
  · simp [hr' x hx]
  · simp [hs']

open Classical in

theorem pure_multilinear {κ : Type} [Fintype κ] (ζ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hζ : ∀ᶠ v in Filter.cofinite, ζ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (T : Finset (Pl F))
    (π : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) :
    ∃ Ψ : SInf F κ →ₗ[ℂ] MultilinearMap ℂ (fun v : T => (κ → Fv F v) → ℂ) ((κ → AF F) → ℂ),
      ∀ f φ, Ψ f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (fun v => if h : v ∈ T then π v (φ ⟨v, h⟩) else ζ v) := by
  choose c hc using fun x => GlobalTheory.PureML.finprod_eq_mul ζ hζ T x
  let P : (κ → AF F) → MultilinearMap ℂ (fun v : T => (κ → Fv F v) → ℂ) ℂ :=
    fun x => (MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap
      (fun v => (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → Fv F v.1) => ℂ) (fun i => evFin F v.1 (x i))).comp (π v))
  refine ⟨{ toFun := fun f => MultilinearMap.pi (fun x => (f (fun i => evI F (x i)) * c x) • P x),
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro f g; ext φ x; simp [add_mul, add_smul]
  · intro a f; ext φ x; simp [mul_assoc, smul_smul]
  · intro f φ; funext x
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hc x (fun v => π v (φ v)) _ (fun v h => by simp [h]) (fun v h => by simp [h])]
    simp [P, MultilinearMap.mkPiAlgebra_apply]
    ring

theorem thetaKer_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om' (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, G.M'.I om' Ψ = 0 → Ψ ∈ N) → ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 Φ' → Φ' ∈ N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM N hN hI Φ' hSo hPM
  classical
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, hj, h0, hΦ, heq⟩ := hPM
  have hz := GlobalTheory.PureTensor.pure_sum_tensor_eq_zero F E σ a (a + a') G.V G.W G.M B.ψ hM.triple.geo.hM T m f φ
    (fun j v hv => (hi j).2.2 v hv) h0.symm R.Pi Rf.Pi R.p (fun v => Rf.p v)
  rw [hz] at heq
  have hs := hM.triple.geo.hM'.std
  have hvac : ∀ v, G.M'.vac v ∈ SB _ := fun v => (hM.triple.geo.hM'.vac v).1
  set S := Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) with hS
  have honto := ((GlobalTheory.T.theta_kernel_coinvariant hKP.base F E σ B a a' G X om om' R Rf hM).1 B.v₁ hM.triple.chars.good).2.2.1 B.τ₁
  obtain ⟨π₁, hπS, hπid, hπp⟩ := exists_proj S (Rf.p' B.v₁) fun ξ => by
    obtain ⟨x, hx, e⟩ := honto ξ
    exact ⟨x, Submodule.subset_span hx, e⟩
  let π : ∀ v : Pl F, ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    Function.update (fun _ => LinearMap.id) B.v₁ π₁
  have hπ1 : π B.v₁ = π₁ := Function.update_self _ _ _
  have hπne : ∀ v, v ≠ B.v₁ → π v = LinearMap.id := fun v hv => Function.update_of_ne hv _ _
  have hπSB : ∀ v, ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), π v χ ∈ SB _ := by
    intro v χ hχ
    by_cases hv : v = B.v₁
    · subst hv; rw [hπ1]; exact GlobalTheory.SoPure.span_soLoc_le _ _ _ (hπS χ)
    · rw [hπne v hv]; exact hχ
  have hev : ∀ᶠ v in Filter.cofinite, π v (G.M'.vac v) = G.M'.vac v := by
    filter_upwards [Filter.eventually_cofinite_ne B.v₁] with v hv
    rw [hπne v hv]; rfl
  obtain ⟨Ψ, hΨ⟩ := pure_multilinear (fun v => π v (G.M'.vac v)) ((hev.and hs).mono fun v hv => hv.1.trans hv.2) T π
  have hext : ∀ s : ∀ v : T, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ i, s i ∈ SB _) →
      (∀ v, (if h : v ∈ T then π v (s ⟨v, h⟩) else π v (G.M'.vac v)) ∈ SB _) ∧
      (∀ᶠ v in Filter.cofinite, (if h : v ∈ T then π v (s ⟨v, h⟩) else π v (G.M'.vac v)) = G.M'.vac v) ∧
      (if h : B.v₁ ∈ T then π B.v₁ (s ⟨B.v₁, h⟩) else π B.v₁ (G.M'.vac B.v₁)) ∈ S := by
    intro s hs
    refine ⟨fun v => ?_, ?_, ?_⟩
    · split_ifs with h
      · exact hπSB v _ (hs _)
      · exact hπSB v _ (hvac v)
    · filter_upwards [hev, T.eventually_cofinite_notMem] with v hv hT
      rw [dif_neg hT, hv]
    · rw [hπ1]
      split_ifs <;> exact hπS _
  have hk1 : ∀ x ∈ G.M'.Pol B.ψ B.emb, ∀ s : ∀ v : T, (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      (∀ i, s i ∈ SB _) → R.p' x = 0 → Ψ x s ∈ N := by
    intro x hx s hs hp
    rw [hΨ]
    exact killInf hKP F E σ B a a' G X om om' R Rf hM N hN _ _ hx (hext s hs).1 (hext s hs).2.1 (hext s hs).2.2 hp
  have hk2 : ∀ x ∈ G.M'.Pol B.ψ B.emb, ∀ s : ∀ v : T, (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      (∀ i, s i ∈ SB _) → ∀ i : T, Rf.p' i (s i) = 0 → Ψ x s ∈ N := by
    rintro x hx s hs ⟨v, hvT⟩ hp
    rw [hΨ]
    by_cases hv : v = B.v₁
    · subst hv
      refine killOne hKP F E σ B a a' G X om om' R Rf hM N hN _ _ hx (hext s hs).1 (hext s hs).2.1 (hext s hs).2.2 ?_
      rw [dif_pos hvT, hπ1, hπp]; exact hp
    · refine killFin hKP F E σ B a a' G X om om' R Rf hM N hN hI _ _ hx (hext s hs).1 (hext s hs).2.1 (hext s hs).2.2 v hv ?_
      rw [dif_pos hvT, hπne v hv]; exact hp
  have key := GlobalTheory.descend_multilinear_mod T (SInf F (Fin a' × Fin (a + a'))) R.Pi ((Fin a' × Fin (a + a') → AF F) → ℂ)
    (fun v : T => (Fin a' × Fin (a + a') → Fv F v) → ℂ) (fun v : T => Rf.Pi v) (G.M'.Pol B.ψ B.emb)
    (fun v => SB _) N R.p' (fun v => Rf.p' v) Ψ hM.real.quot'.onto (fun v => hM.fin.onto' v) hk1 hk2 m' f'
    (fun k v => φ' k v) (fun k => ⟨(hj k).1, fun v => (hj k).2.1 v⟩) heq.symm
  rw [← GlobalTheory.SoPure.atOp_of_mem_so G.M' B.ψ B.τ₁ hs π₁ (fun χ hχ => hπid χ (Submodule.subset_span hχ)) Φ' hSo, hΦ, map_sum]
  convert key using 2 with k
  have hk : ∀ᶠ v in Filter.cofinite, φ' k v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hs, T.eventually_cofinite_notMem] with v hv hT
    rw [(hj k).2.2 v hT, hv]
  rw [hΨ, GlobalTheory.SoPure.atOp_pure B.v₁ π₁ _ _ hk]
  congr 1
  funext v
  have e : (if h : v ∈ T then π v (φ' k v) else π v (G.M'.vac v)) = π v (φ' k v) := by
    split_ifs with h
    · rfl
    · rw [(hj k).2.2 v h]
  refine Eq.trans ?_ e.symm
  by_cases hv : v = B.v₁
  · subst hv; rw [Function.update_self, hπ1]
  · rw [Function.update_of_ne hv, hπne v hv]; rfl

end GlobalTheory.ThetaFacIrrSmall

end
