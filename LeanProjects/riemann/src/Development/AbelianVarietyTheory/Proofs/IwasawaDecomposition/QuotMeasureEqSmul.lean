import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIntegralMulRight

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingNorm

theorem weylDimU_eq {p : ℕ} (lam a : Fin p → ℤ) (h : ∀ i j, lam i - lam j = a i - a j) :
    ((weylDimU lam : ℚ) : ℝ) = Formalism.L2.Geo.weylDim a := by
  unfold weylDimU Formalism.L2.Geo.weylDim
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun j _ => ?_
  have : ((lam i : ℝ) - lam j) = a i - a j := by exact_mod_cast h i j
  rw [this]

theorem sq_eq_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) :
    ((‖x‖ ^ 2 : ℝ) : ℂ) = inner ℂ x x := by
  rw [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K]
  rfl

variable {D : D7}

theorem lab_emb (ρ : D.what₂.Tau) : lab D.what₂.embLL ρ = ρ := by
  have hE : ∀ τ, labE D.what₂.embLL τ = tauE D τ := fun τ => by
    ext x
    exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)
  have h : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (hE ρ)⟩
  unfold lab
  rw [dif_pos h]
  have hs := h.choose_spec
  generalize h.choose = τ at hs
  rw [hE] at hs
  rcases hs with hs | hs
  · have h1 : D.host.sigmaOf (D.eTau τ).1 = D.host.sigmaOf (D.eTau ρ).1 := by
      exact AlgEquiv.ext fun x => D.host.φ₀.injective (DFunLike.congr_fun hs x)
    apply D.eTau.injective
    apply Subtype.ext
    exact (by unfold Host.sigmaOf at h1; exact (EquivLike.injective _) h1)
  · exfalso
    have a := xi_zero_im_pos D τ
    have b := xi_zero_im_pos D ρ
    rw [hs] at a
    simp at a
    linarith

theorem dimK_eq (hK : DV.KapDef D) (i : Fin D.R.m) (τ : D.what₂.Tau) (s : ℕ × ℕ) (hs : s = D.R.sigW ((i : ℕ) + 1)) :
    ((dimK s.1 s.2 (Formalism.L2.NTheta.kapW (D.hc τ) s.1 s.2) : ℚ) : ℝ) =
      Formalism.L2.Geo.weylDim (D.what₂.kaBig ((i : ℕ) + 1) τ) * Formalism.L2.Geo.weylDim (D.what₂.kaSmall ((i : ℕ) + 1) τ) := by
  subst hs
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by
    simp only [Ranks.sigW]; omega
  have hq : i + 1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m := by
    simp only [Ranks.sigW]; omega
  have hodd : Odd ((D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2) := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by omega⟩
  obtain ⟨h1, h2⟩ := hK _ (inR i).1 (inR i).2 τ
  have hc := Formalism.L2.NTheta.kapW_cast (D.hc τ) _ _ hodd
  unfold dimK
  rw [Rat.cast_mul, weylDimU_eq _ (D.what₂.kaBig ((i : ℕ) + 1) τ), weylDimU_eq _ (D.what₂.kaSmall ((i : ℕ) + 1) τ)]
  · intro a b
    have e : ∀ c : Fin (D.R.sigW ((i : ℕ) + 1)).2, DV.aMinusQ D ((i : ℕ) + 1) τ c =
        -Formalism.L2.NTheta.lamAt (D.hc τ) ((D.R.sigW ((i : ℕ) + 1)).1 + c) - DV.eQ D ((i : ℕ) + 1) τ -
          ((D.R.t : ℚ) + 1 + 2 * (c : ℕ)) / 2 := fun c => by
      have := c.2
      unfold DV.aMinusQ Formalism.L2.NTheta.lamAt
      rw [dif_pos (by omega), dif_neg (by omega), dif_pos (by omega), neg_neg]
      congr 4
      omega
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_sub, Int.cast_sub, hc, hc, h2, h2, e, e]
    simp only [Formalism.L2.NTheta.kapQ, Sum.elim_inr]
    ring
  · intro a b
    have e : ∀ n, DV.sigPar D τ n = Formalism.L2.NTheta.lamAt (D.hc τ) n := fun n => by
      unfold DV.sigPar Formalism.L2.NTheta.lamAt
      rfl
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_sub, Int.cast_sub, hc, hc, h1, h1, DV.aPlusQ_eq, DV.aPlusQ_eq, e, e]
    simp only [Formalism.L2.NTheta.kapQ, Sum.elim_inl]
    ring

theorem prod_dimK (hK : DV.KapDef D) (i : Fin D.R.m) :
    (∏ ρ, ((dimK _ _ (kapAt (Wc D i) D.what₂.embLL ρ) : ℚ) : ℂ)) = (Formalism.L2.Geo.dimKap D ((i : ℕ) + 1) : ℝ) := by
  unfold Formalism.L2.Geo.dimKap
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [← dimK_eq hK i ρ _ (D.sp.W_sigval _ (inR i).1 (inR i).2 (tauE D ρ)), Complex.ofReal_ratCast, kapAt, lab_emb]

theorem quotMeasure_eq_smul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = ν 𝓕 • muQ1 V := by
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hp := GlobalTheory.AutomorphicL2Unitary.isVolPair_volPair hP
  have := hp.1.1
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have e := Measure.isMulLeftInvariant_eq_smul ν (volPair V).1
  set c := Measure.haarScalarFactor ν (volPair V).1
  have e1 : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = (c : ENNReal) • muQ V := by
    rw [GlobalTheory.AutomorphicL2Unitary.muQ_eq hP, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have e2 : ν 𝓕 = c * muQ V Set.univ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]
    exact congrArg (fun m : Measure (AutQ V) => m Set.univ) e1
  rw [e1, e2, muQ1, if_pos (show _ ∧ _ from hV), smul_smul, mul_assoc, ENNReal.mul_inv_cancel hV.1 hV.2, mul_one]

theorem integral_star_mul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (φ : GA D V → ℂ) (hφ : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g)
    (ψ : AutQ V → ℂ) (hψ : MemLp ψ 2 (muQ1 V)) (c : ℝ) (h : ∀ q, ‖φ q.out‖ = c * ‖ψ q‖) :
    ∫ g in 𝓕, star (φ g) * φ g ∂ν = (((ν 𝓕).toReal * (c * ‖hψ.toLp ψ‖) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ := hφ
  have e1 := GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕
    (fun q => star (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q) * GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q)
  simp only [hL.descend_mk] at e1
  have e2 : ((‖hψ.toLp ψ‖ ^ 2 : ℝ) : ℂ) = ∫ q, ((‖ψ q‖ ^ 2 : ℝ) : ℂ) ∂muQ1 V := by
    rw [sq_eq_inner, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψ.coeFn_toLp] with q hq
    rw [hq, sq_eq_inner]
  rw [← e1, show GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _ from quotMeasure_eq_smul V hs hν h𝓕, integral_smul_measure, mul_pow,
    Complex.ofReal_mul, Complex.ofReal_mul, e2, ← integral_const_mul, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  show star (φ q.out) * φ q.out = ((c ^ 2 : ℝ) : ℂ) * ((‖ψ q‖ ^ 2 : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, ← mul_pow, ← h, Complex.ofReal_pow]
  exact Complex.conj_mul' _

theorem norm_phiJ (T : CoreJ D) (hL : LawsJ T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j)
    {σ : T.Q.c.F →+* ℂ} (hg : GoodEmb T.Q.c σ) (f : T.cuspA j (wtA w) w.n) :
    ∀ g, ‖T.phiJ j σ (wtA w) (f : T.R j) g‖ = lieFac (T.Q.Dw j) (xiR D) (wtA w) *
      ‖adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f) g‖ := by
  intro g
  rw [CoreJ.phiJ_apply, norm_mul, hL.cUnit j hj σ hg, one_mul, Core.phiAd, Pi.smul_apply, norm_smul,
    Complex.norm_real, Real.norm_of_nonneg (lieFac_pos _ _ _).le]

theorem jFn_apply (T : CoreJ D) {j : ℕ} (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (f : T.cuspA j (wtA w) w.n) :
    ∀ q : AutQ (T.V j σ), jFn (T.V j σ) σ (rdC (T.U j) σ (wtA w) w.n) (T.dict j σ) (T.mu j σ) f q =
      adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f) q.out := by
  intro q
  rfl

theorem integral_phiC (T : CoreJ D) (hL : LawsJ T) (h : LawsCore T.toCore) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j)
    {σ σ' : T.Q.c.F →+* ℂ} (hσ : σ = goodOf T.Q.c σ') {W : HSp D} (hV : T.V j σ = W) (hs : W.SigOK)
    {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν)
    (f : T.cuspA j (wtA w) w.n) (hφ : ∀ γ ∈ GQ W, ∀ g, phiC T hV (wtA w) (f : T.R j) (γ * g) = phiC T hV (wtA w) (f : T.R j) g) :
    ∫ g in 𝓕, star (phiC T hV (wtA w) (f : T.R j) g) * phiC T hV (wtA w) (f : T.R j) g ∂ν =
      (((ν 𝓕).toReal * h.Nl j w σ' (f : T.R j) ^ 2 : ℝ) : ℂ) := by
  have hg : GoodEmb T.Q.c σ := hσ ▸ goodEmb_goodOf _ σ'
  have hm := h.cuspidalL2Subspace j hj σ hg _ _ (dom_wtA w)
  have e : h.Nl j w σ' (f : T.R j) = lieFac (T.Q.Dw j) (xiR D) (wtA w) * ‖(hm f).toLp _‖ := by
    subst hσ
    rw [LawsCore.Nl, dif_pos hj, l2C, dif_pos f.2]
    rfl
  rw [e]
  clear e hσ
  subst hV
  have e2 : phiC T rfl (wtA w) (f : T.R j) = T.phiJ j σ (wtA w) (f : T.R j) := rfl
  rw [e2] at hφ ⊢
  exact integral_star_mul (T.V j σ) hs hν h𝓕 _ hφ _ (hm f) _ fun q =>
    (norm_phiJ T hL hj w hg f q.out).trans (congrArg (_ * ‖·‖) (jFn_apply T w σ f q).symm)

theorem normSq_eq {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    (H : HMod (MMap M)) {N : ℂ} (h : ∀ x y, inner ℂ x y = N * ipM M μ 𝓕 (H.e x) (H.e y)) (v : M.Vec)
    (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x : H.H) :
    ((‖x‖ ^ 2 : ℝ) : ℂ) = N * ∫ g in 𝓕, star (H.e x v g) * H.e x v g ∂μ := by
  by_cases hx : x = 0
  · subst hx
    simp
  have h1 : ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e x) c := by
    by_contra hc
    apply inner_self_ne_zero (𝕜 := ℂ).2 hx
    rw [h, ipM, dif_neg hc, mul_zero]
  rw [(ipM_spec _ _ _ _ _ h1 v v).2, sq_eq_inner, h]
  simp [inner_self_eq_norm_sq_to_K, hv]

theorem norm_jTop : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (h : LawsCore T.toCore), DV.KapDef D → PreChar R → TieIn T R κ v₀ → JEvExists T R κ v₀ → ∀ (i : Fin D.R.m) (f : Cu T κ i), ‖jTop T R κ v₀ i (sg0 D A) f‖ = Real.sqrt ((R.νW i (R.fdW i)).toReal * Formalism.L2.Geo.dimKap D ((i : ℕ) + 1)) * h.Nl ((i : ℕ) + 1) (κ i) T.σ₀ (f : T.R ((i : ℕ) + 1)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ h hK hR ht hj i f
  have hpin : T.Q.PinField := ht.laws.pins.2.2.1
  have e0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hg := base_embedding_good T R ht.alg hpin
  have hV := ht.laws.spaceW _ (inR i) _ hg
  have hσ : res T (sg0 D A) = goodOf T.Q.c T.σ₀ := by
    rw [goodOf, if_pos T.good_σ₀, e0, res_embLL T ht.alg hpin]
  have hev := jTop_good T R κ v₀ hg hV (hj i _ hg hV) f
  obtain ⟨-, hr, hip⟩ := hR.models.HW i (sg0 D A)
  have hm : (R.HW i (sg0 D A)).e (jTop T R κ v₀ i (sg0 D A) f) ∈ R.Wall i (sg0 D A) := hr ▸ ⟨_, rfl⟩
  have ha := ((GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hm).aut (v₀ i (sg0 D A))
  have h1 := normSq_eq (R.HW i (sg0 D A)) hip (v₀ i _) (ht.hv₀ i _).norm (jTop T R κ v₀ i (sg0 D A) f)
  unfold evAt at hev
  rw [hev] at ha h1
  rw [integral_phiC T ht.laws h (inR i) (κ i) hσ hV (D.sp.W_sig _) (hR.models.νW i).1.1 (hR.models.νW i).2 f ha.left,
    show (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) = _ from e0 ▸ prod_dimK hK i, ← Complex.ofReal_mul,
    Complex.ofReal_inj] at h1
  have hN := (h.hNl _ (inR i) (κ i) T.σ₀).nonneg _ f.2
  rw [← Real.sqrt_sq hN, ← Real.sqrt_mul' _ (sq_nonneg _), ← Real.sqrt_sq (norm_nonneg (jTop T R κ v₀ i (sg0 D A) f)), h1]
  congr 1
  ring

end GlobalTheory.ReadingNorm
