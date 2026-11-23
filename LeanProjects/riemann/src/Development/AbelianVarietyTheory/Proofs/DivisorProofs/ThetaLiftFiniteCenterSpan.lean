import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZfinOfThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralSmoothAlongRealLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCountableRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLieDerivativeInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearInPolynomialDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRealLineDerivativeStatement

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.ZFinV

open GlobalTheory.ThK.FiniteLevelDerivatives GlobalTheory.ThetaFacInf GlobalTheory.ThetaFacInf.Fib

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro h0
  obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hy' : star y ≠ 0 := by simpa using hy
  have := h.2.2 (star y) hy'
  rw [star_star, hMy, dotProduct_zero] at this
  simp at this

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem chains (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ _), StrictMono N →
    (∀ i, GlobalTheory.Published.ThetaSubInf G.M B.ψ B.emb om (N i)) → m ≤ L := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hp := GlobalTheory.ThK.Inhab.pairV hT
  refine (hKP.howeDualityReal F E σ hT.base.cm a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om hT.base.std
    hT.geo.hV.herm (fun h0 => det_ne_zero_of_isCartan (hT.geo.hV.cartan w) ?_) hT.geo.hW.skew
    (fun h0 => det_ne_zero_of_isCartan (hT.geo.hW.cartan w) ?_) hp.resX hp.resW hp.hX hp.hW hT.weil B.emb hT.geo.hV.cartan
    hT.geo.hW.cartan).1
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]

theorem I_mul_right (Φ : Fn F a (a + a')) (h k : UA σ G.W.J) : G.M.I om Φ (h * k) = G.M.I om (om (1, k) Φ) h := by
  unfold Model.I theta
  congr 1; funext g
  rw [show ((g, h * k) : UA σ G.V.J × UA σ G.W.J) = (g, h) * (1, k) by simp, map_mul, Module.End.mul_apply]

theorem zfin_pure (hσ : ∀ x, σ (σ x) = x) (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {c : E} (hc : c ≠ 0) (hcc : σ c = -c)
    (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hev : ∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) {f : SInf F (Fin a × Fin (a + a'))} (hf : f ∈ G.M.Pol B.ψ B.emb) :
    FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ (c • G.W.J.map σ) z ∧
      u = dop z (fun x => G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ((toGAd hσ G.W.J hc).symm x))}) := by
  have hp := GlobalTheory.ThK.Inhab.pairV hT
  have hs : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hev.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2
  have hD : ∀ f ∈ G.M.Pol B.ψ B.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ PolData B G.M := fun f hf =>
    Submodule.subset_span ⟨f, hf, φ, hSB, hev, rfl⟩
  have lin := GlobalTheory.T.theta_integral_linear_in_polynomial_datum F E σ B a a' G X om om' hKP hT
  have lin0 : G.M.I om 0 = 0 := by
    have := lin 0 (zero_mem _) 0 (zero_mem _) 1
    simpa using this
  let T₀ : G.M.Pol B.ψ B.emb →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ) :=
    { toFun := fun g x => G.M.I om (pureL φ g.1) ((toGAd hσ G.W.J hc).symm x)
      map_add' := fun g g' => funext fun x => by
        have := congrFun (lin _ (hD _ g.2) _ (hD _ g'.2) 1) ((toGAd hσ G.W.J hc).symm x)
        rw [one_smul, one_smul] at this
        rw [Submodule.coe_add, map_add]
        exact this
      map_smul' := fun r g => funext fun x => by
        have := congrFun (lin _ (hD _ g.2) 0 (zero_mem _) r) ((toGAd hσ G.W.J hc).symm x)
        rw [add_zero, lin0, add_zero] at this
        rw [Submodule.coe_smul, map_smul]
        exact this }
  obtain ⟨T, hT₀⟩ := LinearMap.exists_extend T₀
  have eT : ∀ g ∈ G.M.Pol B.ψ B.emb, T g = fun x => G.M.I om (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) ((toGAd hσ G.W.J hc).symm x) :=
    fun g hg => LinearMap.congr_fun hT₀ ⟨g, hg⟩
  obtain ⟨hP1, hP2, hP3, hP4⟩ := GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hT
  rw [← eT f hf]
  refine zfin_of_thetaSub hσ hT.base.cm G.M B.ψ B.emb om hc
    (GlobalTheory.T.polynomial_data_countable_rank hKP.base F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hp) (chains hKP hT) hP1 hP2 hP3 hP4 T
    (fun g hg => ?_) (fun γ hγ g hg g₁ hg₁ h => ?_) (fun k hk g hg g₁ hg₁ h => ?_) (fun γ hγ g hg g₁ hg₁ h x => ?_)
    (fun k hk g hg g₁ hg₁ h => ?_) hf
  · rw [eT g hg]
    exact GlobalTheory.T.theta_lift_real_line_derivative F E σ hσ B a a' G X om om' hKP hT c hc hcc _ (hD g hg)
  · have e : derL om (fun t => γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ :=
      funext fun y => (hasDerivAt_pure φ hSB hs h y).deriv
    have := (GlobalTheory.T.theta_integral_lie_derivative_invariant F E σ B a a' G X om om' hKP hT _ (hD g hg) [γ] (by simpa using hγ)).2 (by simp)
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, e] at this
    rw [eT g₁ hg₁, this]
    rfl
  · rw [eT g hg, eT g₁ hg₁, ← acts_pure φ hSB hs h,
      GlobalTheory.ThetaIntegralInv.integral_translate hKP.base hp k _ (GlobalTheory.ThKDer.polData_le hT.geo.hM (hD g hg))]
  · obtain ⟨Φ₂, h2, d2⟩ := GlobalTheory.ThKDer.exists_der hKP hT hγ _ (hD g₁ hg₁)
    have := GlobalTheory.ThKDer.hasDerivAt_I hKP hT hγ (hD g hg) (hD g₁ hg₁) h2
      (GlobalTheory.ThKDer.kerDer F E σ B a a' G X om om' hKP hT γ hγ g hg g₁ h φ hSB hev) d2 ((toGAd hσ G.W.J hc).symm x)
    simpa only [eT g hg, eT g₁ hg₁, map_mul, MulEquiv.symm_apply_apply] using this
  · rw [eT g hg, eT g₁ hg₁, ← acts_pure φ hSB hs h]
    funext x
    simp only [map_mul, MulEquiv.symm_apply_apply, I_mul_right]

theorem zfin_thetaIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ (c • G.W.J.map σ) z ∧ f = dop z (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x))}) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcc Φ hΦ
  have lin := GlobalTheory.T.theta_integral_linear_in_polynomial_datum F E σ B a a' G X om om' hKP hT
  have lin0 : G.M.I om 0 = 0 := by
    have := lin 0 (zero_mem _) 0 (zero_mem _) 1
    simpa using this
  have sm := GlobalTheory.T.theta_lift_real_line_derivative F E σ hσ B a a' G X om om' hKP hT c hc hcc
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, hf, φ, hSB, hev, rfl⟩ := h
    exact zfin_pure hσ hKP hT hc hcc φ hSB hev hf
  | zero =>
    rw [lin0]
    exact zfin_zero
  | add Φ Ψ hΦ hΨ h1 h2 =>
    have := lin Φ hΦ Ψ hΨ 1
    rw [one_smul, one_smul] at this
    rw [this]
    exact zfin_add (sm Φ hΦ) (sm Ψ hΨ) h1 h2
  | smul r Φ hΦ h1 =>
    have := lin Φ hΦ 0 (zero_mem _) r
    rw [add_zero, lin0, add_zero] at this
    rw [this]
    exact zfin_smul r h1

end GlobalTheory.ThK.ZFinV

end
