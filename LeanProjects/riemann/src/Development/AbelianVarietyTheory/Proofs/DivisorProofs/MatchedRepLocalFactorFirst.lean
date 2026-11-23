import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompFinEqZeroOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParameterSkewHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianTwistToHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit

noncomputable section

namespace GlobalTheory.ThKAdmAut

section Chart

open NumberField Matrix Topology Filter Formalism.MainNotions.S Formalism.REAL GlobalTheory.Dec
open scoped ContDiff

def IsLine (I : AutInst) (γ : ℝ → I.Ginf) : Prop :=
  ∃ (v : InfinitePlace I.F) (Y : Matrix (Fin I.n) (Fin I.n) ℂ),
    ∀ t : ℝ, uMat (γ t v) = NormedSpace.exp (t • Y) ∧ ∀ u, u ≠ v → γ t u = 1

theorem prod_mulSingle {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, Monoid (M i)] (y : ∀ i, M i) :
    ∀ l : List ι, l.Nodup → ∀ u, (l.map fun v => (Pi.mulSingle v (y v) : ∀ i, M i)).prod u = if u ∈ l then y u else 1 := by
  intro l
  induction l with
  | nil => intro _ u; simp
  | cons v l ih =>
    intro h u
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih h.2]
    by_cases e : u = v
    · subst e; simp [h.1]
    · simp [e]

theorem contDiffAt_list {I : AutInst} {a : I.Ginf → ℂ}
    (h : ∀ (k : ℕ) (γ : Fin k → ℝ → I.Ginf), (∀ i, IsLine I (γ i)) → ∀ x,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => a (x * (List.ofFn fun i => γ i (t i)).prod))
    {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] (z₀ : T) (l : List ((ℝ → I.Ginf) × (T → ℝ)))
    (hl : ∀ p ∈ l, IsLine I p.1 ∧ ContDiffAt ℝ ∞ p.2 z₀) (x : I.Ginf) :
    ContDiffAt ℝ ∞ (fun z => a (x * (l.map fun p => p.1 (p.2 z)).prod)) z₀ := by
  have h1 := (h l.length (fun i => (l.get i).1) (fun i => (hl _ (List.get_mem l i)).1) x).contDiffAt.comp z₀
    (contDiffAt_pi.2 fun i => (hl _ (List.get_mem l i)).2)
  convert h1 using 1
  funext z
  conv_lhs => rw [← List.ofFn_get l, List.map_ofFn]
  rfl

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem exists_chart_at (I : AutInst) [DecidableEq (InfinitePlace I.F)] (x : I.Ginf) (v : InfinitePlace I.F) :
    ∃ l : List ((ℝ → I.Ginf) × ((InfinitePlace I.F → Fin I.n → Fin I.n → ℂ) → ℝ)),
      (∀ p ∈ l, IsLine I p.1 ∧ ContDiffAt ℝ ∞ p.2 (fun v i j => uMat (x v) i j)) ∧
      ∀ᶠ g in 𝓝 x, (l.map fun p => p.1 (p.2 fun v i j => uMat (g v) i j)).prod = Pi.mulSingle v ((x v)⁻¹ * g v) := by
  set J := Jm (I.ε v) with hJ
  have h2 : J * J = 1 := Jm_mul_self _
  have hH : Jᴴ = J := Jm_conjTranspose _
  let s : Matrix (Fin I.n) (Fin I.n) ℂ →ₗ[ℝ] Matrix (Fin I.n) (Fin I.n) ℂ :=
    { toFun := fun x => J * xᴴ * J
      map_add' := fun x y => by rw [conjTranspose_add, mul_add, add_mul]
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  have hs : ∀ x, s x = J * xᴴ * J := fun _ => rfl
  have hJJ : ∀ x : Matrix (Fin I.n) (Fin I.n) ℂ, J * (J * x) = x := fun x => by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  obtain ⟨N, Y, Ψ, hY, hΨ, hE⟩ := GlobalTheory.BesselMapOne.exists_chart s
    (fun a => by simp only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc, hJJ, h2,
      Matrix.mul_one])
    (fun a b => by simp only [hs, conjTranspose_mul, Matrix.mul_assoc, hJJ]) (by simp [hs, h2])
  have hYl : ∀ i, (Y i)ᴴ * J + J * Y i = 0 := fun i => by
    have := congrArg (J * ·) (hY i)
    simp only [hs, Matrix.mul_assoc, hJJ, Matrix.mul_neg] at this
    rw [this, neg_add_cancel]
  have hd : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).1 (IsUnit.of_mul_eq_one _ h2)
  have hex : ∀ i (t : ℝ), ∃ u : UJ (I.ε v), uMat u = NormedSpace.exp (t • Y i) := fun i t => by
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Y i)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (X := t • Y i) hd (by
      rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hYl, smul_zero])
    exact ⟨⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, hu⟩
  choose u hu using hex
  have hun : ∀ g : UJ (I.ε v), s (uMat g) * uMat g = 1 := fun g => by
    have hg' : (uMat g)ᴴ * J * uMat g = J := g.2
    rw [hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hg', h2]
  let A : (InfinitePlace I.F → Fin I.n → Fin I.n → ℂ) →ₗ[ℝ] Matrix (Fin I.n) (Fin I.n) ℂ :=
    { toFun := fun p => uMat (x v)⁻¹ * Matrix.of (p v)
      map_add' := fun _ _ => Matrix.mul_add _ _ _
      map_smul' := fun c p => Matrix.mul_smul _ c (Matrix.of (p v)) }
  have hAg : ∀ g : I.Ginf, A (fun v i j => uMat (g v) i j) = uMat ((x v)⁻¹ * g v) := fun g => rfl
  have hA : A (fun v i j => uMat (x v) i j) = 1 := by rw [hAg, inv_mul_cancel]; rfl
  refine ⟨List.ofFn fun i => (fun t => Pi.mulSingle v (u i t), fun p => Ψ (A p) i), fun p hp => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
    refine ⟨⟨v, Y i, fun t => ⟨by simp [hu], fun w hw => Pi.mulSingle_eq_of_ne hw _⟩⟩, ?_⟩
    exact contDiffAt_pi.1 (ContDiffAt.comp (g := Ψ) _ (by show ContDiffAt ℝ ∞ Ψ (A _); rwa [hA])
      (LinearMap.toContinuousLinearMap A).contDiff.contDiffAt) i
  · have ht : Tendsto (fun g : I.Ginf => uMat ((x v)⁻¹ * g v)) (𝓝 x) (𝓝 1) := by
      have hc : Continuous fun g : I.Ginf => uMat ((x v)⁻¹ * g v) :=
        (Units.continuous_val.comp continuous_subtype_val).comp (continuous_const.mul (continuous_apply v))
      have := hc.tendsto x
      rwa [inv_mul_cancel] at this
    filter_upwards [ht.eventually hE] with g q
    have q' := q (hun _)
    rw [List.map_ofFn]
    have e1 : (List.ofFn fun i => u i (Ψ (uMat ((x v)⁻¹ * g v)) i)).prod = (x v)⁻¹ * g v := by
      apply Subtype.ext; apply Units.ext
      let φ : UJ (I.ε v) →* Matrix (Fin I.n) (Fin I.n) ℂ := (Units.coeHom _).comp (UJ (I.ε v)).subtype
      show φ _ = uMat _
      refine Eq.trans ?_ q'
      rw [map_list_prod, List.map_ofFn]
      congr 2
      funext i
      exact hu _ _
    rw [← e1]
    have := map_list_prod (MonoidHom.mulSingle (fun w => UJ (I.ε w)) v) (List.ofFn fun i => u i (Ψ (uMat ((x v)⁻¹ * g v)) i))
    rw [List.map_ofFn] at this
    exact this.symm

theorem smoothInf_of_lines {I : AutInst} {a : I.Ginf → ℂ}
    (h : ∀ (k : ℕ) (γ : Fin k → ℝ → I.Ginf), (∀ i, IsLine I (γ i)) → ∀ x,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => a (x * (List.ofFn fun i => γ i (t i)).prod)) : SmoothInf I a := by
  classical
  intro x
  choose l hl hl' using exists_chart_at I x
  refine ⟨_, contDiffAt_list h _ (Finset.univ.toList.flatMap l) (fun p hp => ?_) x, ?_⟩
  · obtain ⟨v, -, hv⟩ := List.mem_flatMap.1 hp
    exact hl v p hv
  · filter_upwards [Filter.eventually_all.2 hl'] with g hg
    congr 1
    rw [List.map_flatMap, List.flatMap_def, List.prod_flatten, List.map_map]
    have : (List.prod ∘ fun v => (l v).map fun p => p.1 (p.2 fun v i j => uMat (g v) i j)) =
        fun v => (Pi.mulSingle v ((x v)⁻¹ * g v) : I.Ginf) := funext hg
    rw [this]
    funext w
    rw [Pi.mul_apply, prod_mulSingle (fun v => (x v)⁻¹ * g v) _ (Finset.nodup_toList _)]
    simp

end Chart

section Transport

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThKAdm GlobalTheory.ThK.SquareIntegrability GlobalTheory.SiegelSet GlobalTheory.Orb GlobalTheory.Dec GlobalTheory.Count
open Formalism.MainNotions.S (AutInst uMat)
open scoped ContDiff NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}
  {B : Base F E} {W : Spc F E d} {L : Subgroup (UA σ W.J)} {I : AutInst} {g : ℕ} {e : I.GA →* UA σ W.J}

theorem rank_eq (h : IsTransp B W L I g e) : d = I.n := by
  obtain ⟨ι, Q, Q', hQ, -⟩ := h.frame
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  have h1 := Matrix.trace_mul_comm (Q v) (Q' v)
  rw [(hQ v).1, (hQ v).2, Matrix.trace_one, Matrix.trace_one, Fintype.card_fin, Fintype.card_fin] at h1
  exact_mod_cast h1

theorem isRealLine_transp (hcm : IsCMExt F E σ) (hσ : ∀ x, σ (σ x) = x) {c : E} (hc : c ≠ 0) (h : IsTransp B W L I g e)
    {γ : ℝ → I.Ginf} (hγ : IsLine I γ) :
    IsRealLine σ (c • W.J.map σ) fun t => toGAd hσ W.J hc (e (γ t, 1)) := by
  obtain rfl := rank_eq h
  obtain ⟨ι, Q, Q', hQ, hfr⟩ := h.frame
  obtain ⟨v, Y, hY⟩ := hγ
  have ha : ∀ (x : I.Ginf) u, archMat σ (c • W.J.map σ) (B.emb (ι u))
      (projArch σ _ (ι u) (toGAd hσ W.J hc (e (x, 1)))) = Q u * uMat (x u) * Q' u := fun x u => hfr x u
  have hZ : ∀ t : ℝ, archMat σ (c • W.J.map σ) (B.emb (ι v))
      (projArch σ _ (ι v) (toGAd hσ W.J hc (e (γ t, 1)))) = NormedSpace.exp (t • (Q v * Y * Q' v)) := fun t => by
    have hi : (Q v)⁻¹ = Q' v := Matrix.inv_eq_left_inv (hQ v).1
    rw [ha, (hY t).1, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hi,
      Matrix.exp_conj _ _ (IsUnit.of_mul_eq_one _ (hQ v).2)]
  refine ⟨ι v, B.emb (ι v), Q v * Y * Q' v,
    GlobalTheory.ThK.OneParamLie.lie_of_archMat_eq_exp F E σ hcm _ _ _ _ _ _ hZ, fun t => ⟨_, ?_, hZ t⟩⟩
  refine GAd_ext σ _ (fun w => ?_) fun u => ?_
  · obtain ⟨u, rfl⟩ := ι.surjective w
    by_cases e₁ : u = v
    · subst e₁; rw [projArch_embArch_self]
    · rw [projArch_embArch_ne σ _ (fun h' => e₁ (ι.injective h'))]
      apply (archEquiv (c • W.J.map σ) hcm (B.emb (ι u))).injective
      apply Subtype.ext; apply Units.ext
      rw [← archMat_eq_archEquiv, ← archMat_eq_archEquiv, ha, map_one, (hY t).2 u e₁]
      exact (congrArg (· * Q' u) (Matrix.mul_one (Q u))).trans (hQ u).2
  · rw [proj_embArch]
    exact mem_infPts_iff_forall.1 (GlobalTheory.ThK.FiniteLevelDerivatives.toGAd_mem_infPts hσ W hc (h.real _)) u

theorem opNorm_le_exp {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : (opNorm y : ℝ) ≤ Real.exp (dOp y) :=
  Real.le_exp_log _

theorem dOp_nonneg {n : ℕ} {ε : Fin n → Bool} (x : Formalism.REAL.UJ ε) : 0 ≤ dOp (uMat x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : uMat x = 0 := Subsingleton.elim _ _
    simp [this, dOp]
  · exact ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 x x hn).1

theorem ht_transp_le (hcm : IsCMExt F E σ) (h : IsTransp B W L I g e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : I.Ginf, (ht (e (y, 1)) : ℝ) ≤ C * Real.exp (dSum I y) := by
  obtain rfl := rank_eq h
  have hσ := sigma_sigma hcm
  obtain ⟨ι, Q, Q', hQ, hfr⟩ := h.frame
  refine ⟨∏ v, max 1 ((opNorm (Q v) : ℝ) * opNorm (Q' v)), by positivity, fun y => ?_⟩
  have hfin : ∀ v, htFin F v (Formalism.UG.bc (compFin F E v) (e (y, 1)).1) = 1 := fun v => by
    have h1 := mem_infPts_iff_forall.1 (GlobalTheory.ThK.FiniteLevelDerivatives.toGAd_mem_infPts hσ W one_ne_zero (h.real y)) v
    have h2 : Formalism.UG.bc (compFin F E v) (e (y, 1)).1 = 1 := congrArg Subtype.val h1
    rw [h2]
    exact htOf_eq_one.2 ⟨normFin_one_le F v, normFin_one_le F v⟩
  have hn : ∀ (x : I.Ginf) v, (normInf F (ι v) (Formalism.UG.bc (compInf F E (ι v)) (e (x, 1)).1).1 : ℝ) ≤
      max 1 ((opNorm (Q v) : ℝ) * opNorm (Q' v)) * Real.exp (dOp (uMat (x v))) := fun x v => by
    rw [normInf_eq_opNorm hcm (B.emb (ι v))]
    have h1 : (Formalism.UG.bc (compInf F E (ι v)) (e (x, 1)).1).1.map (infEmb (B.emb (ι v))) =
        Q v * uMat (x v) * Q' v := hfr x v
    rw [h1]
    have h2 : (opNorm (Q v * uMat (x v) * Q' v) : ℝ) ≤ opNorm (Q v) * opNorm (uMat (x v)) * opNorm (Q' v) := by
      exact_mod_cast (opNorm_mul_le _ _).trans (mul_le_mul' (opNorm_mul_le _ _) le_rfl)
    refine h2.trans ?_
    rw [mul_right_comm]
    exact mul_le_mul (le_max_right _ _) (opNorm_le_exp _) (NNReal.coe_nonneg _) (by positivity)
  rw [ht, heightGL, finprod_eq_one_of_forall_eq_one hfin, mul_one, ← ι.prod_comp, dSum, Real.exp_sum,
    ← Finset.prod_mul_distrib, NNReal.coe_prod]
  refine Finset.prod_le_prod (fun _ _ => NNReal.coe_nonneg _) fun v _ => ?_
  rw [htInf, htOf, NNReal.coe_max, NNReal.coe_max]
  refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_exp (dOp_nonneg _))) (max_le (hn y v) ?_)
  have h3 := hn y⁻¹ v
  have h4 : dOp (uMat (y⁻¹ v)) = dOp (uMat (y v)) := by
    rw [← GlobalTheory.Count.Cartan.dOp_inv (y v).2]
    exact congrArg dOp (Matrix.coe_units_inv _)
  have h5 : e (y⁻¹, 1) = (e (y, 1))⁻¹ := by rw [← map_inv, Prod.inv_mk, inv_one]
  rw [h4, h5, Subgroup.coe_inv, map_inv] at h3
  exact h3

end Transport

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.SquareIntegrability

theorem isSmoothMG_theta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (L : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), GlobalTheory.ThKAdm.IsLevel G.W L → ∀ (I : Formalism.MainNotions.S.AutInst) (g : ℕ) (e : I.GA →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), 1 ≤ g → GlobalTheory.ThKAdm.IsTransp B G.W L I g e → ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), (∀ l ∈ L, om' (1, l) Ψ = Ψ) → GlobalTheory.Dec.IsSmoothMG I g (fun x => G.M'.I om' Ψ (e x)) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM L _ I g e _ he Ψ hΨ hL
  have hT := hM.triple
  have hcm := hT.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨x₀, hx⟩ := GlobalTheory.SkewToHerm.exists_sigma_ne σ hcm
  have hc : x₀ - σ x₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hcc : σ (x₀ - σ x₀) = -(x₀ - σ x₀) := by rw [map_sub, hσ, neg_sub]
  refine ⟨fun γ hγ x => ?_, fun k hk x => ?_, fun xf => ⟨smoothInf_of_lines fun k γ hγ x => ?_, ?_⟩⟩
  · simp only [map_mul]
    exact (GlobalTheory.T.continuous_left_invariant_dual hKP F E σ B a a' G X om om' hT Ψ hΨ).2 _ (he.rat γ hγ) _
  · simp only [map_mul]
    rw [← GlobalTheory.ThetaFacCompl.I_transl, hL _ (he.lev k hk)]
  · have h1 := GlobalTheory.T.polynomial_theta_kernel_smooth F E σ hσ B a a' G X om om' hKP hT _ hc hcc Ψ hΨ k _
      (fun i => isRealLine_transp hcm hσ hc he (hγ i)) (toGAd hσ G.W.J hc (e (x, xf)))
    convert h1 using 3 with t
    let φ : I.Ginf →* UA σ G.W.J := e.comp (MonoidHom.inl _ _)
    have h2 : ((x * (List.ofFn fun i => γ i (t i)).prod, xf) : I.GA) =
        (x, xf) * MonoidHom.inl _ _ (List.ofFn fun i => γ i (t i)).prod := by simp
    simp only [h2, map_mul, map_list_prod, List.map_ofFn, MulEquiv.symm_apply_apply, Function.comp_def,
      MonoidHom.inl_apply]
  · obtain ⟨N, hN⟩ := GlobalTheory.T.polynomial_theta_kernel_moderate_growth F E σ hσ B a a' G X om om' hKP hT _ hc hcc Ψ hΨ
    obtain ⟨C, hC⟩ := hN [] (by simp)
    obtain ⟨C', hC0, hC'⟩ := ht_transp_le hcm he
    refine ⟨max C 0 * (C' * ht (e (1, xf))) ^ N, N, fun y => ?_⟩
    have h1 : ‖G.M'.I om' Ψ (e (y, xf))‖ ≤ C * (ht (e (y, xf)) : ℝ) ^ N := hC (toGAd hσ G.W.J hc (e (y, xf)))
    have h2 : (ht (e (y, xf)) : ℝ) ≤ C' * ht (e (1, xf)) * Real.exp (GlobalTheory.Dec.dSum I y) := by
      have e1 : e (y, xf) = e (y, 1) * e (1, xf) := by rw [← map_mul]; simp
      have h3 : (ht (e (y, xf)) : ℝ) ≤ ht (e (y, 1)) * ht (e (1, xf)) := by
        rw [e1]; exact_mod_cast heightGL_mul_le F (e (y, 1)).1 (e (1, xf)).1
      refine h3.trans ?_
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right (hC' y) (NNReal.coe_nonneg _)
    refine h1.trans ?_
    rw [Real.exp_nat_mul, mul_assoc, ← mul_pow]
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h2 _) (by positivity) (le_max_right _ _)

end GlobalTheory.ThKAdmAut

end
