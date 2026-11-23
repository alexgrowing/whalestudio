import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZfinOfThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRealLineDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineCorrespondsToLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCountableRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatchingExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralIteratedRealDerivativesStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV

open GlobalTheory.WeakHolFamily GlobalTheory.ThK.FiniteLevelDerivatives

noncomputable section

namespace GlobalTheory.ThK.ZonePolynomials

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem unifPoly {ι : Type} (A : Submodule ℂ (ι → GAd σ J → ℂ)) (hsm : ∀ Ψ ∈ A, ∀ i, IsSm σ J (Ψ i))
    (hder : ∀ γ, IsRealLine σ J γ → ∀ Ψ ∈ A, (fun i => lineDer γ (Ψ i)) ∈ A) (K : Set (GAd σ J))
    (hK : ∀ k ∈ K, k ∈ infPts σ J) (hKA : ∀ k ∈ K, ∀ Ψ ∈ A, (fun i x => Ψ i (x * k)) ∈ A)
    (hr : Module.rank ℂ A ≤ Cardinal.aleph0)
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (ι → GAd σ J → ℂ)), StrictMono N →
      (∀ i, N i ≤ A ∧ (∀ γ, IsRealLine σ J γ → ∀ Ψ ∈ N i, (fun j => lineDer γ (Ψ j)) ∈ N i) ∧
        ∀ k ∈ K, ∀ Ψ ∈ N i, (fun j x => Ψ j (x * k)) ∈ N i) → m ≤ L)
    (z : List (ℝ → GAd σ J) →₀ ℂ) (hz : IsCentral σ J z) :
    ∃ p : Polynomial ℂ, p.Monic ∧ ∀ Ψ ∈ A, ∀ i,
      ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • (dop z)^[j] (Ψ i) = 0 := by
  let D : ∀ γ, IsRealLine σ J γ → Module.End ℂ A := fun γ hγ =>
    { toFun := fun u => ⟨fun i => lineDer γ (u.1 i), hder γ hγ _ u.2⟩
      map_add' := fun u v => Subtype.ext (funext fun i => lineDer_add (hsm _ u.2 i) (hsm _ v.2 i) hγ)
      map_smul' := fun c u => Subtype.ext (funext fun i => lineDer_smul c (u.1 i) γ) }
  let R : ∀ k ∈ K, Module.End ℂ A := fun k hk =>
    { toFun := fun u => ⟨fun i x => u.1 i (x * k), hKA k hk _ u.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let S : Set (Module.End ℂ A) := {s | ∃ γ hγ, s = D γ hγ} ∪ {s | ∃ k hk, s = R k hk}
  have hfold : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∀ Ψ ∈ A,
      (fun i => l.foldr lineDer (Ψ i)) ∈ A := fun l hl Ψ hΨ => by
    induction l with
    | nil => exact hΨ
    | cons γ l ih => exact hder γ (hl γ List.mem_cons_self) _ (ih fun γ' h => hl γ' (List.mem_cons_of_mem _ h))
  have hTmem : ∀ Ψ ∈ A, (fun i => dop z (Ψ i)) ∈ A := fun Ψ hΨ => by
    have e : (fun i => dop z (Ψ i)) = ∑ l ∈ z.support, z l • fun i => l.foldr lineDer (Ψ i) := by
      funext i
      rw [dop_eq_sum, Finset.sum_apply]
      rfl
    rw [e]
    exact A.sum_mem fun l hl => A.smul_mem _ (hfold l (hz.1 l hl) Ψ hΨ)
  let T : Module.End ℂ A :=
    { toFun := fun u => ⟨fun i => dop z (u.1 i), hTmem _ u.2⟩
      map_add' := fun u v => Subtype.ext (funext fun i => dop_add hz.1 (hsm _ u.2 i) (hsm _ v.2 i))
      map_smul' := fun c u => Subtype.ext (funext fun i => dop_smul z c (u.1 i)) }
  have hL' : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ A), StrictMono N →
      (∀ i, ∀ s ∈ S, ∀ x ∈ N i, s x ∈ N i) → m ≤ L := by
    obtain ⟨L, hL⟩ := hL
    refine ⟨L, fun m N hN hS => hL m (fun i => (N i).map A.subtype)
      ((Submodule.map_strictMono_of_injective A.injective_subtype).comp hN) fun i => ⟨Submodule.map_subtype_le _ _, ?_, ?_⟩⟩
    · rintro γ hγ _ ⟨u, hu, rfl⟩
      exact ⟨_, hS i _ (Or.inl ⟨γ, hγ, rfl⟩) u hu, rfl⟩
    · rintro k hk _ ⟨u, hu, rfl⟩
      exact ⟨_, hS i _ (Or.inr ⟨k, hk, rfl⟩) u hu, rfl⟩
  haveI := GlobalTheory.FiniteLengthCommutant.finiteDimensional_centralizer A S hr hL'
  have hTc : T ∈ Subalgebra.centralizer ℂ S := by
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ (⟨γ, hγ, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact LinearMap.ext fun u => Subtype.ext (funext fun i =>
        GlobalTheory.T.central_operator_commutes_line_derivative F E σ n J z hz (u.1 i) (hsm _ u.2 i) γ hγ)
    · exact LinearMap.ext fun u => Subtype.ext (funext fun i => funext fun g =>
        (hz.2 (u.1 i) (hsm _ u.2 i) k (hK k hk) g).symm)
  let T' : Subalgebra.centralizer ℂ S := ⟨T, hTc⟩
  have hint : IsIntegral ℂ T' := Algebra.IsIntegral.isIntegral T'
  refine ⟨minpoly ℂ T', minpoly.monic hint, fun Ψ hΨ i => ?_⟩
  have h0 : Polynomial.aeval T (minpoly ℂ T') = 0 := by
    have := minpoly.aeval ℂ T'
    have e := Polynomial.aeval_subalgebra_coe (minpoly ℂ T') (Subalgebra.centralizer ℂ S) T'
    rw [this] at e
    simpa using e.symm
  have hpow : ∀ j (u : A), ((T ^ j) u).1 i = (dop z)^[j] (u.1 i) := by
    intro j
    induction j with
    | zero => intro u; rfl
    | succ j ih =>
      intro u
      rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
      rfl
  have h1 := congrArg (fun Q : Module.End ℂ A => (Q ⟨Ψ, hΨ⟩).1 i) h0
  simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul, LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply,
    Finset.sum_apply, Pi.smul_apply] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hpow]

section Conc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ}

def FinD (G : Geo σ a a') : Set (∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ) :=
  {φ | (∀ v, φ v ∈ SB _) ∧ ∀ᶠ v in Filter.cofinite, φ v = G.M.vac v}

theorem pure_add' {κ : Type} [Fintype κ] (f g : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul' {κ : Type} [Fintype κ] (r : ℂ) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (r • f) φ = r • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem I_om_one' {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (om : Rep σ Y W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (k h : UA σ W.J) : M.I om (om (1, k) Φ) h = M.I om Φ (h * k) := by
  unfold Model.I theta
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (om (1, k) Φ)) = thetaSum F (om (g, h * k) Φ)
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem det_ne_zero_of_cartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro h0
  obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hy' : star y ≠ 0 := by simpa using hy
  have := h.2.2 (star y) hy'
  rw [star_star, hMy, dotProduct_zero] at this
  simp at this

theorem pure_poly (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hKP : KP) (hT : IsTriple B G X om om') {c : E} (hc : c ≠ 0) (hcσ : σ c = -c)
    (z : List (ℝ → GAd σ (c • G.W.J.map σ)) →₀ ℂ) (hz : IsCentral σ (c • G.W.J.map σ) z) :
    ∃ p : Polynomial ℂ, p.Monic ∧ ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ φ ∈ FinD G,
      ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j • (dop z)^[j] (fun x => G.M.I om (pure f φ) ((toGAd hσ G.W.J hc).symm x)) = 0 := by
  classical
  set P := G.M.Pol B.ψ B.emb with hPdef
  set e := toGAd hσ G.W.J hc with he
  have hstd : ∀ φ ∈ FinD G, ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x : Fin a × Fin (a + a') → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    fun φ hφ => (hφ.2.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2
  have hmem : ∀ f ∈ P, ∀ φ ∈ FinD G, pure f φ ∈ PolData B G.M :=
    fun f hf φ hφ => Submodule.subset_span ⟨f, hf, φ, hφ.1, hφ.2, rfl⟩
  have hrest : ∀ φ ∈ FinD G, ∀ f : SInf F (Fin a × Fin (a + a')),
      Rest (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) :=
    fun φ hφ f => GlobalTheory.ThK.EvUniqInf.rest_pure f φ hφ.1 (hstd φ hφ)
  have hlin := GlobalTheory.ThetaProjectionLie.linT hKP hT
  obtain ⟨hP1, hP2, hP3, hP4⟩ := GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hT
  have hW1 : ∀ γ ∈ Lines σ G.W, ∀ f ∈ P, ∀ f₁ ∈ P,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → ∀ φ ∈ FinD G, ∀ h,
        HasDerivAt (fun t : ℝ => G.M.I om (pure f φ) (h * γ (Multiplicative.ofAdd t))) (G.M.I om (pure f₁ φ) h) 0 :=
    fun γ hγ f hf f₁ hf₁ hd φ hφ => GlobalTheory.ThetaProjectionLie.lieWT hKP hT γ hγ _ (hmem f hf φ hφ) _ (hmem f₁ hf₁ φ hφ)
      (fun x => hd _ (hrest φ hφ f) x)
  have hW2 : ∀ k ∈ KInf σ G.W B.emb, ∀ f : SInf F (Fin a × Fin (a + a')), ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      Acts (evI F) (om (1, k)) f f₁ → ∀ φ ∈ FinD G, ∀ h, G.M.I om (pure f₁ φ) h = G.M.I om (pure f φ) (h * k) := by
    intro k _ f f₁ hd φ hφ h
    have e1 : pure f₁ φ = om (1, k) (pure f φ) := (hd _ (hrest φ hφ f)).symm
    rw [e1, I_om_one']
  have hX1 : ∀ γ ∈ Lines σ G.V, ∀ f ∈ P, ∀ f₁ ∈ P,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → ∀ φ ∈ FinD G, G.M.I om (pure f₁ φ) = 0 :=
    fun γ hγ f hf f₁ hf₁ hd φ hφ => GlobalTheory.ThetaProjectionLie.lieVT hKP hT γ hγ _ (hmem f hf φ hφ) _ (hmem f₁ hf₁ φ hφ)
      (fun x => hd _ (hrest φ hφ f) x)
  have hX2 : ∀ k ∈ KInf σ G.V B.emb, ∀ f ∈ P, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      Acts (evI F) (om (k, 1)) f f₁ → ∀ φ ∈ FinD G, G.M.I om (pure f₁ φ) = G.M.I om (pure f φ) := by
    intro k hk f hf f₁ hd φ hφ
    have e1 : pure f₁ φ = om (k, 1) (pure f φ) := (hd _ (hrest φ hφ f)).symm
    rw [e1]
    exact (GlobalTheory.ThetaProjectionLie.invVT hKP hT _ (hmem f hf φ hφ)).2 k hk
  let TL : P →ₗ[ℂ] (FinD G → GAd σ (c • G.W.J.map σ) → ℂ) :=
    { toFun := fun f φ x => G.M.I om (pure f.1 φ.1) (e.symm x)
      map_add' := fun f g => by
        funext φ x
        have h := (hlin _ (hmem f.1 f.2 φ.1 φ.2) _ (hmem g.1 g.2 φ.1 φ.2) 0).1
        simp only [Submodule.coe_add, Pi.add_apply]
        rw [pure_add', h]
        rfl
      map_smul' := fun r f => by
        funext φ x
        have h := (hlin _ (hmem f.1 f.2 φ.1 φ.2) _ (hmem f.1 f.2 φ.1 φ.2) r).2
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply]
        rw [pure_smul', h]
        rfl }
  have hsm : ∀ f : P, ∀ φ : FinD G, IsSm σ (c • G.W.J.map σ) (TL f φ) := fun f φ k γ hγ g =>
    GlobalTheory.T.theta_lift_real_line_derivative F E σ hσ B a a' G X om om' hKP hT c hc hcσ _ (hmem f.1 f.2 φ.1 φ.2) k γ hγ g
  have hp := GlobalTheory.ThKConst.isPair_big hT
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdV : G.V.J.det ≠ 0 := by
    have h1 := det_ne_zero_of_cartan (hT.geo.hV.cartan w)
    intro h0
    apply h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hdW : G.W.J.det ≠ 0 := by
    have h1 := det_ne_zero_of_cartan (hT.geo.hW.cartan w)
    intro h0
    apply h1
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  obtain ⟨L, hHowe⟩ := (hKP.howeDualityReal F E σ hT.base.cm a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om hT.base.std
    hT.geo.hV.herm hdV hT.geo.hW.skew hdW hp.resX hp.resW hp.hX hp.hW hT.weil B.emb hT.geo.hV.cartan
    hT.geo.hW.cartan).1
  obtain ⟨p, hpm, hp0⟩ := unifPoly (LinearMap.range TL)
    (by rintro _ ⟨f, rfl⟩ φ; exact hsm f φ)
    (by
      rintro γ hγ _ ⟨f, rfl⟩
      obtain ⟨γL, hγL, eγ⟩ := GlobalTheory.T.real_line_corresponds_to_line F E σ hσ hT.base.cm G.W c hc γ hγ
      have eγ' : ∀ t, e.symm (γ t) = γL (Multiplicative.ofAdd t) := eγ
      obtain ⟨f₁, hf₁, hd, -⟩ := hP3 γL hγL f.1 f.2
      refine ⟨⟨f₁, hf₁⟩, funext fun φ => funext fun x => ?_⟩
      have h1 := (hW1 γL hγL f.1 f.2 f₁ hf₁ hd φ.1 φ.2 (e.symm x)).deriv
      show G.M.I om (pure f₁ φ.1) (e.symm x) = deriv (fun t => G.M.I om (pure f.1 φ.1) (e.symm (x * γ t))) 0
      simp only [map_mul, eγ']
      exact h1.symm)
    (e '' KInf σ G.W B.emb)
    (by rintro _ ⟨k, hk, rfl⟩; exact GlobalTheory.ThK.FiniteLevelDerivatives.toGAd_mem_infPts hσ G.W hc hk.1)
    (by
      rintro _ ⟨k, hk, rfl⟩ _ ⟨f, rfl⟩
      obtain ⟨f₁, hf₁, hd, -⟩ := hP4 k hk f.1 f.2
      refine ⟨⟨f₁, hf₁⟩, funext fun φ => funext fun x => ?_⟩
      show G.M.I om (pure f₁ φ.1) (e.symm x) = G.M.I om (pure f.1 φ.1) (e.symm (x * e k))
      rw [map_mul, MulEquiv.symm_apply_apply]
      exact hW2 k hk f.1 f₁ hd φ.1 φ.2 _)
    ((rank_range_le TL).trans (GlobalTheory.T.polynomial_data_countable_rank hKP.base F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hp))
    (by
      refine ⟨L, fun m N hN hS => hHowe m (fun i => ((N i).comap TL).map P.subtype) (fun i j hij => ?_) fun i => ?_⟩
      · refine lt_of_le_of_ne (Submodule.map_mono (Submodule.comap_mono (hN hij).le)) fun heq => (hN hij).not_ge ?_
        intro u hu
        obtain ⟨f, rfl⟩ := (hS j).1 hu
        have heq' : ((N i).comap TL).map P.subtype = ((N j).comap TL).map P.subtype := heq
        have h1 : f.1 ∈ ((N j).comap TL).map P.subtype := ⟨f, hu, rfl⟩
        rw [← heq'] at h1
        obtain ⟨g, hg, hgf⟩ := h1
        have : g = f := Subtype.ext hgf
        subst this
        exact hg
      · refine ⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩
        · intro γ hγ f hf f₁ hd
          have hf₁ := hP1 γ hγ f hf f₁ hd
          refine ⟨⟨f₁, hf₁⟩, ?_, rfl⟩
          have h0 : TL ⟨f₁, hf₁⟩ = 0 := funext fun φ => funext fun x => by
            show G.M.I om (pure f₁ φ.1) (e.symm x) = 0
            rw [hX1 γ hγ f hf f₁ hf₁ hd φ.1 φ.2]
            rfl
          show TL ⟨f₁, hf₁⟩ ∈ N i
          rw [h0]
          exact zero_mem _
        · intro k hk f hf f₁ hd
          have hf₁ := hP2 k hk f hf f₁ hd
          refine ⟨⟨f₁, hf₁⟩ - ⟨f, hf⟩, ?_, rfl⟩
          have h0 : TL (⟨f₁, hf₁⟩ - ⟨f, hf⟩) = 0 := by
            rw [map_sub, sub_eq_zero]
            funext φ x
            show G.M.I om (pure f₁ φ.1) (e.symm x) = G.M.I om (pure f φ.1) (e.symm x)
            rw [hX2 k hk f hf f₁ hd φ.1 φ.2]
          show TL (⟨f₁, hf₁⟩ - ⟨f, hf⟩) ∈ N i
          rw [h0]
          exact zero_mem _
        · rintro γ hγ _ ⟨⟨f, hf⟩, hfN, rfl⟩ f₁ hd
          obtain ⟨g₂, hg₂, -, hu⟩ := hP3 γ hγ f hf
          obtain rfl := hu f₁ hd
          refine ⟨⟨f₁, hg₂⟩, ?_, rfl⟩
          obtain ⟨k, δ, hδ, eδ⟩ := GlobalTheory.T.real_line_factor_as_product_lines F E σ hσ hT.base.cm G.W c hc γ hγ
          have e2 : TL ⟨f₁, hg₂⟩ = ∑ j, fun φ => lineDer (δ j) (TL ⟨f, hf⟩ φ) := funext fun φ => funext fun x => by
            rw [Finset.sum_apply, Finset.sum_apply]
            have h1 := hW1 γ hγ f hf f₁ hg₂ hd φ.1 φ.2 (e.symm x)
            have h2 := GlobalTheory.T.has_deriv_at_product_of_real_lines F E σ hT.base.cm _ _ k δ hδ (TL ⟨f, hf⟩ φ) (hsm _ φ) x
            have e3 : (fun t : ℝ => G.M.I om (pure f φ.1) (e.symm x * γ (Multiplicative.ofAdd t))) =
                fun t => TL ⟨f, hf⟩ φ (x * (List.ofFn fun i => δ i t).prod) := funext fun t => by
              show _ = G.M.I om (pure f φ.1) (e.symm (x * _))
              rw [← eδ, map_mul, MulEquiv.symm_apply_apply]
            rw [e3] at h1
            exact h1.unique h2
          show TL ⟨f₁, hg₂⟩ ∈ N i
          rw [e2]
          exact Submodule.sum_mem _ fun j _ => (hS i).2.1 _ (hδ j) _ hfN
        · rintro k hk _ ⟨⟨f, hf⟩, hfN, rfl⟩ f₁ hd
          obtain ⟨g₂, hg₂, -, hu⟩ := hP4 k hk f hf
          obtain rfl := hu f₁ hd
          refine ⟨⟨f₁, hg₂⟩, ?_, rfl⟩
          have e2 : TL ⟨f₁, hg₂⟩ = fun φ x => TL ⟨f, hf⟩ φ (x * e k) := funext fun φ => funext fun x => by
            show G.M.I om (pure f₁ φ.1) (e.symm x) = G.M.I om (pure f φ.1) (e.symm (x * e k))
            rw [map_mul, MulEquiv.symm_apply_apply]
            exact hW2 k hk f f₁ hd φ.1 φ.2 _
          show TL ⟨f₁, hg₂⟩ ∈ N i
          rw [e2]
          exact (hS i).2.2 _ ⟨k, hk, rfl⟩ _ hfN)
    z hz
  exact ⟨p, hpm, fun f hf φ hφ => hp0 (TL ⟨f, hf⟩) ⟨_, rfl⟩ ⟨φ, hφ⟩⟩

end Conc

end GlobalTheory.ThK.ZonePolynomials

open GlobalTheory.ThK.ZonePolynomials GlobalTheory.ThK.FiniteLevelDerivatives

namespace GlobalTheory.ThK.ZoneV

theorem zone : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ z, IsCentral σ (c • G.W.J.map σ) z →
    ∃ (N : ℕ) (b : Fin N → ℂ), ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      (dop z)^[N] (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) =
        ∑ i : Fin N, b i • (dop z)^[i.val] (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) := by
  intro hKP F E _ _ _ _ _ σ hσ B a a' G X om om' hT c hc hcσ z hz
  classical
  obtain ⟨p, hpm, hp⟩ := pure_poly hσ hKP hT hc hcσ z hz
  set e := toGAd hσ G.W.J hc with he
  let TΦ : Fn F a (a + a') → GAd σ (c • G.W.J.map σ) → ℂ := fun Φ x => G.M.I om Φ (e.symm x)
  have hlin := GlobalTheory.ThetaProjectionLie.linT hKP hT
  have Tadd : ∀ Φ ∈ PolData B G.M, ∀ Ψ ∈ PolData B G.M, TΦ (Φ + Ψ) = TΦ Φ + TΦ Ψ := fun Φ hΦ Ψ hΨ => by
    funext x
    show G.M.I om (Φ + Ψ) _ = _
    rw [(hlin Φ hΦ Ψ hΨ 0).1]
    rfl
  have Tsmul : ∀ Φ ∈ PolData B G.M, ∀ r : ℂ, TΦ (r • Φ) = r • TΦ Φ := fun Φ hΦ r => by
    funext x
    show G.M.I om (r • Φ) _ = _
    rw [(hlin Φ hΦ Φ hΦ r).2]
    rfl
  have T0 : TΦ 0 = 0 := by
    have h := Tsmul 0 (zero_mem _) 0
    rwa [zero_smul, zero_smul] at h
  have Tsum : ∀ (s : Finset (List (ℝ → GAd σ (c • G.W.J.map σ))))
      (Ψ : List (ℝ → GAd σ (c • G.W.J.map σ)) → Fn F a (a + a')), (∀ l ∈ s, Ψ l ∈ PolData B G.M) →
      TΦ (∑ l ∈ s, Ψ l) = ∑ l ∈ s, TΦ (Ψ l) := by
    intro s Ψ hΨ
    induction s using Finset.induction_on with
    | empty => simpa using T0
    | insert l s hl ih =>
      rw [Finset.sum_insert hl, Finset.sum_insert hl,
        Tadd _ (hΨ l (Finset.mem_insert_self _ _)) _ (Submodule.sum_mem _ fun k hk => hΨ k (Finset.mem_insert_of_mem hk)),
        ih fun k hk => hΨ k (Finset.mem_insert_of_mem hk)]
  have hsmT : ∀ Φ ∈ PolData B G.M, IsSm σ (c • G.W.J.map σ) (TΦ Φ) := fun Φ hΦ k γ hγ g =>
    GlobalTheory.T.theta_lift_real_line_derivative F E σ hσ B a a' G X om om' hKP hT c hc hcσ Φ hΦ k γ hγ g
  have hstep : ∀ Φ ∈ PolData B G.M, ∃ Φ' ∈ PolData B G.M, dop z (TΦ Φ) = TΦ Φ' := by
    intro Φ hΦ
    have hw := fun l (hl : l ∈ z.support) => GlobalTheory.T.theta_integral_iterated_real_derivatives F E σ hσ B a a' G X om om' hKP hT c hc hcσ Φ hΦ l (hz.1 l hl)
    refine ⟨∑ l ∈ z.support, z l • (l.map (back hσ G.W.J hc)).foldr (derR om) Φ,
      Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (hw l hl).1, ?_⟩
    rw [dop_eq_sum, Tsum _ _ (fun l hl => Submodule.smul_mem _ _ (hw l hl).1)]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Tsmul _ (hw l hl).1]
    congr 1
    exact (hw l hl).2
  have hiter : ∀ j, ∀ Φ ∈ PolData B G.M, ∃ Φ' ∈ PolData B G.M, (dop z)^[j] (TΦ Φ) = TΦ Φ' := by
    intro j
    induction j with
    | zero => exact fun Φ hΦ => ⟨Φ, hΦ, rfl⟩
    | succ j ih =>
      intro Φ hΦ
      obtain ⟨Φ₁, h1, e1⟩ := ih Φ hΦ
      obtain ⟨Φ₂, h2, e2⟩ := hstep Φ₁ h1
      exact ⟨Φ₂, h2, by rw [Function.iterate_succ_apply', e1, e2]⟩
  have hadd : ∀ j, ∀ Φ ∈ PolData B G.M, ∀ Ψ ∈ PolData B G.M,
      (dop z)^[j] (TΦ (Φ + Ψ)) = (dop z)^[j] (TΦ Φ) + (dop z)^[j] (TΦ Ψ) := by
    intro j
    induction j with
    | zero => exact fun Φ hΦ Ψ hΨ => Tadd Φ hΦ Ψ hΨ
    | succ j ih =>
      intro Φ hΦ Ψ hΨ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih Φ hΦ Ψ hΨ]
      obtain ⟨Φ₁, h1, e1⟩ := hiter j Φ hΦ
      obtain ⟨Ψ₁, h2, e2⟩ := hiter j Ψ hΨ
      rw [e1, e2]
      exact dop_add hz.1 (hsmT _ h1) (hsmT _ h2)
  have hsmul : ∀ j (r : ℂ) (u : GAd σ (c • G.W.J.map σ) → ℂ), (dop z)^[j] (r • u) = r • (dop z)^[j] u := by
    intro j
    induction j with
    | zero => exact fun r u => rfl
    | succ j ih =>
      intro r u
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, dop_smul]
  have hzero : ∀ j, (dop z)^[j] (0 : GAd σ (c • G.W.J.map σ) → ℂ) = 0 := fun j => by
    have h := hsmul j 0 0
    rwa [zero_smul, zero_smul] at h
  have hEv : ∀ Φ ∈ PolData B G.M,
      ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • (dop z)^[j] (TΦ Φ) = 0 := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, hf, φ, h1, h2, rfl⟩ := h
      exact hp f hf φ ⟨h1, h2⟩
    | zero => simp [T0, hzero]
    | add Φ Ψ hΦ hΨ h1 h2 =>
      simp only [hadd _ Φ hΦ Ψ hΨ, smul_add, Finset.sum_add_distrib]
      rw [h1, h2, add_zero]
    | smul r Φ hΦ h1 =>
      simp only [Tsmul Φ hΦ r, hsmul, smul_comm _ r]
      rw [← Finset.smul_sum, h1, smul_zero]
  refine ⟨p.natDegree, fun i => -p.coeff i, fun Φ hΦ => ?_⟩
  have h0 := hEv Φ hΦ
  rw [Finset.sum_range_succ, hpm.coeff_natDegree, one_smul] at h0
  have h1 : (dop z)^[p.natDegree] (TΦ Φ) =
      -∑ j ∈ Finset.range p.natDegree, p.coeff j • (dop z)^[j] (TΦ Φ) := by
    rw [← sub_eq_zero, sub_neg_eq_add]
    exact (add_comm _ _).trans h0
  show (dop z)^[p.natDegree] (TΦ Φ) = ∑ i : Fin p.natDegree, -p.coeff i • (dop z)^[i.val] (TΦ Φ)
  rw [h1, Finset.sum_range (fun j => p.coeff j • (dop z)^[j] (TΦ Φ)), ← Finset.sum_neg_distrib]
  simp only [neg_smul]

end GlobalTheory.ThK.ZoneV
