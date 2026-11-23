import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZfinOfThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralOperatorCommutesLineDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataThetaLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCountableRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineCorrespondsToLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedDataTensorDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDerivativeLineW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDerivativeLineV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralKInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToGAdInfPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivativeStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open GlobalTheory.WeakHolFamily GlobalTheory.ThK.FiniteLevelDerivatives

noncomputable section

namespace GlobalTheory.ThKCentreSmall

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section General

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

private theorem unifPoly {ι : Type} (A : Submodule ℂ (ι → GAd σ J → ℂ)) (hsm : ∀ Ψ ∈ A, ∀ i, IsSm σ J (Ψ i))
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

private def smSub (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) : Submodule ℂ (GAd σ J → ℂ) where
  carrier := {f | IsSm σ J f}
  zero_mem' := smoothLines_zero (J := J)
  add_mem' := fun ha hb => smoothLines_add (J := J) ha hb
  smul_mem' := fun c _ ha => smoothLines_smul (J := J) c ha

theorem isSm_dop {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) {f : GAd σ J → ℂ}
    (hf : IsSm σ J f) : IsSm σ J (dop z f) := by
  rw [dop_eq_sum]
  exact (smSub σ J).sum_mem fun l hl => (smSub σ J).smul_mem _ (smoothLines_foldr (J := J) hf l (hz l hl))

private theorem iterate_dop_sum {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ)
    {ι : Type} (s : Finset ι) (ψ : ι → GAd σ J → ℂ) (hψ : ∀ i, IsSm σ J (ψ i)) (j : ℕ) :
    (dop z)^[j] (∑ i ∈ s, ψ i) = ∑ i ∈ s, (dop z)^[j] (ψ i) := by
  let Z : Module.End ℂ (smSub σ J) :=
    { toFun := fun u => ⟨dop z u.1, isSm_dop hz u.2⟩
      map_add' := fun u v => Subtype.ext (dop_add hz u.2 v.2)
      map_smul' := fun c u => Subtype.ext (dop_smul z c u.1) }
  have hpow : ∀ j (u : smSub σ J), ((Z ^ j) u).1 = (dop z)^[j] u.1 := by
    intro j
    induction j with
    | zero => intro u; rfl
    | succ j ih =>
      intro u
      rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
      rfl
  have h := congrArg Subtype.val (map_sum (Z ^ j) (fun i => (⟨ψ i, hψ i⟩ : smSub σ J)) s)
  rw [hpow, Submodule.coe_sum, Submodule.coe_sum] at h
  simpa only [hpow] using h

end General

variable {a a' : ℕ}

private def FinD (B : Base F E) (G : Geo σ a a') : Set (∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
  {φ | (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) ∧ φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁}

private theorem I_mul {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (o : Rep σ Y W) (Φ : Fn F n d)
    (k h : UA σ W.J) : M.I o (o (1, k) Φ) h = M.I o Φ (h * k) := by
  simp only [Model.I, theta]
  congr 1
  funext g
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

private theorem howe_chain {B : Base F E} (hKP : KP) {n d r s r' s' : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W}
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

private theorem pure_poly (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hKP : KP) (hT : IsTriple B G X om om') {c : E} (hc : c ≠ 0) (hcσ : σ c = -c)
    (z : List (ℝ → GAd σ (c • G.W.J.map σ)) →₀ ℂ) (hz : IsCentral σ (c • G.W.J.map σ) z) :
    ∃ p : Polynomial ℂ, p.Monic ∧ ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ φ ∈ FinD B G,
      ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j • (dop z)^[j] (fun x => G.M'.I om' (pure f φ) ((toGAd hσ G.W.J hc).symm x)) = 0 := by
  classical
  have hP := RealUniq.isPair_V' hT
  obtain ⟨hA1, hA2, hA3, hA4⟩ := GlobalTheory.T.polynomial_datum_action_of_pair hKP.base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP
  obtain ⟨L, hL⟩ := howe_chain hKP hP
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.pol_data_theta_linear F E σ B a a' G X om om' hKP hT
  have hs : ∀ φ : FinD B G, ∀ᶠ v in Filter.cofinite,
      φ.1 v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    fun φ => (φ.2.2.1.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2
  have hD : ∀ φ : FinD B G, ∀ f ∈ G.M'.Pol B.ψ B.emb,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ.1 ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ := fun φ f hf =>
    ⟨Submodule.subset_span ⟨f, hf, φ.1, φ.2.1, φ.2.2.1, rfl⟩, Submodule.subset_span ⟨f, φ.1, φ.2.1, φ.2.2.1, φ.2.2.2, rfl⟩⟩
  obtain ⟨T, hTf⟩ : ∃ T : G.M'.Pol B.ψ B.emb →ₗ[ℂ] (FinD B G → GAd σ (c • G.W.J.map σ) → ℂ),
      ∀ f (hf : f ∈ G.M'.Pol B.ψ B.emb), T ⟨f, hf⟩ =
        fun φ x => G.M'.I om' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ.1) ((toGAd hσ G.W.J hc).symm x) :=
    ⟨LinearMap.pi fun φ => LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ Λ ∘ₗ
      LinearMap.codRestrict _ (GlobalTheory.ThetaFacInf.pureL φ.1 ∘ₗ (G.M'.Pol B.ψ B.emb).subtype) (fun f => hD φ f.1 f.2),
      fun f hf => funext fun φ => funext fun x => congrFun (hΛ ⟨_, hD φ f hf⟩) _⟩
  have hsm : ∀ f (hf : f ∈ G.M'.Pol B.ψ B.emb) φ, IsSm σ (c • G.W.J.map σ) (T ⟨f, hf⟩ φ) := fun f hf φ => by
    rw [hTf]
    exact GlobalTheory.ThAutSmall.Smooth.isSm_theta_small F E σ hσ B a a' G X om om' hKP hT c hc hcσ _ (hD φ f hf)
  have hW1 : ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ f₁ ∈ G.M'.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) f f₁ → ∀ φ : FinD B G, ∀ h,
        HasDerivAt (fun t : ℝ => G.M'.I om' (pure f φ.1) (h * γ (Multiplicative.ofAdd t))) (G.M'.I om' (pure f₁ φ.1) h) 0 :=
    fun γ hγ f hf f₁ hf₁ hd φ => GlobalTheory.ThetaDerivTriple.hasDerivAt_thetaIntegral_triple F E σ B a a' G X om om' hKP hT γ hγ _
      (hD φ f hf) _ (hD φ f₁ hf₁) (GlobalTheory.ThetaFacInf.Fib.hasDerivAt_pure φ.1 φ.2.1 (hs φ) hd)
  have hW2 : ∀ k, ∀ f (hf : f ∈ G.M'.Pol B.ψ B.emb) f₁ (hf₁ : f₁ ∈ G.M'.Pol B.ψ B.emb),
      Acts (evI F) (om' (1, k)) f f₁ → T ⟨f₁, hf₁⟩ = fun φ x => T ⟨f, hf⟩ φ (x * toGAd hσ G.W.J hc k) := by
    intro k f hf f₁ hf₁ h
    funext φ x
    rw [hTf, hTf]
    simp only [map_mul, MulEquiv.symm_apply_apply]
    rw [← GlobalTheory.ThetaFacInf.Fib.acts_pure φ.1 φ.2.1 (hs φ) h]
    exact I_mul _ _ _ _ _
  obtain ⟨p, hpm, hp0⟩ := unifPoly (LinearMap.range T)
    (by rintro _ ⟨⟨f, hf⟩, rfl⟩ φ; exact hsm f hf φ)
    (by
      rintro γ hγ _ ⟨⟨f, hf⟩, rfl⟩
      obtain ⟨γL, hγL, eγ⟩ := GlobalTheory.T.real_line_corresponds_to_line F E σ hσ hT.base.cm G.W c hc γ hγ
      obtain ⟨D, hDm, hDi⟩ := hA3 γL hγL
      refine ⟨⟨D f, hDm f hf⟩, funext fun φ => funext fun x => ?_⟩
      have h1 := (hW1 γL hγL f hf _ (hDm f hf) ((hDi f hf _).2 rfl) φ ((toGAd hσ G.W.J hc).symm x)).deriv
      rw [hTf, hTf]
      simp only [lineDer, map_mul, eγ]
      exact h1.symm)
    (toGAd hσ G.W.J hc '' KInf σ G.W B.emb)
    (by rintro _ ⟨k, hk, rfl⟩; exact GlobalTheory.T.unitary_to_GAd_inf_points F E σ hσ _ G.W c hc k hk.1)
    (by
      rintro _ ⟨k, hk, rfl⟩ _ ⟨⟨f, hf⟩, rfl⟩
      obtain ⟨D, hDm, hDi⟩ := hA4 k hk
      exact ⟨⟨D f, hDm f hf⟩, hW2 k f hf _ (hDm f hf) ((hDi f hf _).2 rfl)⟩)
    ((rank_range_le T).trans (GlobalTheory.T.polynomial_data_countable_rank hKP.base F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP))
    (by
      refine ⟨L, fun m N hN hS => hL m (fun i => ((N i).comap T).map (G.M'.Pol B.ψ B.emb).subtype) (fun i j hij => ?_)
        fun i => ?_⟩
      · refine Submodule.map_strictMono_of_injective (G.M'.Pol B.ψ B.emb).injective_subtype ?_
        have h := hN hij
        refine lt_of_le_of_ne (Submodule.comap_mono h.le) fun e => h.ne ?_
        rw [← Submodule.map_comap_eq_self (hS i).1, ← Submodule.map_comap_eq_self (hS j).1, e]
      have mk : ∀ f (hf : f ∈ G.M'.Pol B.ψ B.emb), T ⟨f, hf⟩ ∈ N i →
          f ∈ ((N i).comap T).map (G.M'.Pol B.ψ B.emb).subtype := fun f hf h => ⟨⟨f, hf⟩, h, rfl⟩
      refine ⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩
      · intro γ hγ f hf f₁ h
        obtain ⟨D, hDm, hDi⟩ := hA1 γ hγ
        have h₁ : f₁ ∈ G.M'.Pol B.ψ B.emb := (hDi f hf f₁).1 h ▸ hDm f hf
        refine mk f₁ h₁ ?_
        have e : T ⟨f₁, h₁⟩ = 0 := by
          rw [hTf]
          funext φ x
          rw [GlobalTheory.ThKLieTriple.lie_kills F E σ B a a' G X om om' hKP hT γ hγ _ (hD φ f hf) _ (hD φ f₁ h₁)
            (GlobalTheory.ThetaFacInf.Fib.hasDerivAt_pure φ.1 φ.2.1 (hs φ) h)]
          rfl
        rw [e]
        exact (N i).zero_mem
      · intro k hk f hf f₁ h
        obtain ⟨D, hDm, hDi⟩ := hA2 k hk
        have h₁ : f₁ ∈ G.M'.Pol B.ψ B.emb := (hDi f hf f₁).1 h ▸ hDm f hf
        refine mk _ (Submodule.sub_mem _ h₁ hf) ?_
        have e : T ⟨f₁, h₁⟩ = T ⟨f, hf⟩ := by
          rw [hTf, hTf]
          funext φ
          rw [← GlobalTheory.ThetaFacInf.Fib.acts_pure φ.1 φ.2.1 (hs φ) h,
            GlobalTheory.T.theta_integral_K_invariant F E σ B a a' G X om om' hKP hT k hk _ (hD φ f hf)]
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
        have e : T ⟨f₁, h₁⟩ = ∑ j, fun φ => lineDer (β j) (T ⟨f, hf⟩ φ) := by
          funext φ g
          have d1 := hder _ (hsm f hf φ) g
          have d2 := hW1 γ hγ f hf f₁ h₁ h φ ((toGAd hσ G.W.J hc).symm g)
          rw [Finset.sum_apply, Finset.sum_apply]
          rw [hTf] at d1
          simp only [map_mul, MulEquiv.symm_apply_apply] at d1
          rw [hTf, hTf]
          exact d2.unique d1
        rw [e]
        exact Submodule.sum_mem _ fun j _ => (hS i).2.1 _ (hβ j) _ hfN'
      · rintro k hk _ ⟨⟨f, hf⟩, hfN, rfl⟩ f₁ h
        obtain ⟨D, hDm, hDi⟩ := hA4 k hk
        have h₁ : f₁ ∈ G.M'.Pol B.ψ B.emb := (hDi f hf f₁).1 h ▸ hDm f hf
        refine mk f₁ h₁ ?_
        rw [hW2 k f hf f₁ h₁ h]
        exact (hS i).2.2 _ ⟨k, hk, rfl⟩ _ hfN)
    z hz
  refine ⟨p, hpm, fun f hf φ hφ => ?_⟩
  have h := hp0 (T ⟨f, hf⟩) ⟨_, rfl⟩ ⟨φ, hφ⟩
  rwa [hTf] at h

theorem exists_monic (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hKP : KP) (hT : IsTriple B G X om om') {c : E} (hc : c ≠ 0) (hcσ : σ c = -c)
    (z : List (ℝ → GAd σ (c • G.W.J.map σ)) →₀ ℂ) (hz : IsCentral σ (c • G.W.J.map σ) z) :
    ∃ (N : ℕ) (b : Fin N → ℂ), ∀ Φ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      (dop z)^[N] (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) =
        ∑ i : Fin N, b i • (dop z)^[i.val] (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) := by
  obtain ⟨p, hpm, hp⟩ := pure_poly hσ hKP hT hc hcσ z hz
  refine ⟨p.natDegree, fun i => -p.coeff i, fun Φ hΦ => ?_⟩
  obtain ⟨m, f, φ, hgood, rfl⟩ := GlobalTheory.T.polarized_data_tensor_decomposition F E σ B a a' G X om om' hT Φ hΦ
  have hD : ∀ i, pure (f i) (φ i) ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ := fun i =>
    ⟨Submodule.subset_span ⟨f i, (hgood i).1, φ i, (hgood i).2.1, (hgood i).2.2.1, rfl⟩,
      Submodule.subset_span ⟨f i, φ i, (hgood i).2.1, (hgood i).2.2.1, (hgood i).2.2.2, rfl⟩⟩
  obtain ⟨Lin, hLin⟩ := GlobalTheory.T.pol_data_theta_linear F E σ B a a' G X om om' hKP hT
  let θi : Fin m → GAd σ (c • G.W.J.map σ) → ℂ := fun i x =>
    G.M'.I om' (pure (f i) (φ i)) ((toGAd hσ G.W.J hc).symm x)
  have hI : G.M'.I om' (∑ i, pure (f i) (φ i)) = ∑ i, G.M'.I om' (pure (f i) (φ i)) := by
    have h1 := hLin ⟨∑ i, pure (f i) (φ i), Submodule.sum_mem _ fun i _ => hD i⟩
    have h2 : (⟨∑ i, pure (f i) (φ i), Submodule.sum_mem _ fun i _ => hD i⟩ :
        ↥(PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) = ∑ i, ⟨pure (f i) (φ i), hD i⟩ := by
      ext1; simp
    rw [← h1, h2, map_sum]
    exact Finset.sum_congr rfl fun i _ => hLin _
  have hsum : (fun x => G.M'.I om' (∑ i, pure (f i) (φ i)) ((toGAd hσ G.W.J hc).symm x)) = ∑ i, θi i := by
    funext x; rw [hI]; simp [θi, Finset.sum_apply]
  have hsm : ∀ i, IsSm σ (c • G.W.J.map σ) (θi i) := fun i =>
    GlobalTheory.ThAutSmall.Smooth.isSm_theta_small F E σ hσ B a a' G X om om' hKP hT c hc hcσ _ (hD i)
  have h0 : ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • (dop z)^[j] (∑ i, θi i) = 0 := by
    simp only [iterate_dop_sum hz.1 _ θi hsm, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ => hp (f i) (hgood i).1 (φ i) (hgood i).2
  rw [hsum]
  rw [Finset.sum_range_succ, hpm.coeff_natDegree, one_smul] at h0
  rw [eq_neg_of_add_eq_zero_right h0, Finset.sum_range (fun j => p.coeff j • (dop z)^[j] (∑ i, θi i)), ← Finset.sum_neg_distrib]
  simp only [neg_smul]

end GlobalTheory.ThKCentreSmall

end
