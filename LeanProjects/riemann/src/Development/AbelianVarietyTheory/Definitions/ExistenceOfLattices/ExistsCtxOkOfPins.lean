import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsInfEmb
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel

noncomputable section

namespace GlobalTheory.Member.Inhab

section Sign

open NumberField Formalism.BasicNotions ComplexConjugate Matrix Formalism.L2.Pj Formalism.L2.Pj.DatLin
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Classical.propDecidable

theorem sqrt_im_pos (D : D7) : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [hφ]
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
  simpa using hd

set_option maxHeartbeats 1600000 in

theorem domFor_one (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) (hI : DatInt D j) :
    DomFor D j ((1 : ℤ) • intForm (efQ D j) hI) := by
  classical
  have hc : ∀ τ : cmTypeOfSqrt D, 0 < ((((1 : ℤ) : ℤ) : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0).im :=
    fun τ => by have h := xi0_embedding_im_pos D τ τ.2; rwa [if_pos (sqrt_im_pos D)] at h
  obtain ⟨θ, hθ⟩ : ∃ θ : (ℝ ⊗[ℤ] latW D j) ≃ₗ[ℝ] (cmTypeOfSqrt D → Fin (D.sp.W j).rank → ℂ),
      ∀ x, θ x = thW D j x := ⟨LinearEquiv.ofBijective _ (thW_bijective D j), fun _ => rfl⟩
  have hsig : ∀ τ : cmTypeOfSqrt D, ∃ K : Matrix (Fin (D.sp.W j).rank) (Fin (D.sp.W j).rank) ℂ,
      (∀ u, K *ᵥ (K *ᵥ u) = -u) ∧
      (∀ u w, star (K *ᵥ u) ⬝ᵥ (GW D j τ *ᵥ (K *ᵥ w)) = star u ⬝ᵥ (GW D j τ *ᵥ w)) ∧
      (∀ u, u ≠ 0 → ∃ ρ : ℝ, 0 < ρ ∧ star (K *ᵥ u) ⬝ᵥ (GW D j τ *ᵥ u) = -(Complex.I * ρ)) ∧
      K.trace = Complex.I * (((D.R.sigW j).1 : ℂ) - (D.R.sigW j).2) := by
    intro τ
    have h1 := D.sp.W_sig j (τ : D.host.E →+* ℂ)
    rw [D.sp.W_sigval j hj.1 hj.2] at h1
    obtain ⟨e, P, hP⟩ := h1
    exact exists_cplx_str _ _ _ e P hP
  choose K hK1 hK2 hK3 hK4 using hsig
  have hr : (D.sp.W j).rank = (D.R.sigW j).1 + (D.R.sigW j).2 := by
    rw [D.sp.W_rank j hj.1 hj.2]
    have := D.R.m_add_three_le_k
    simp only [Ranks.sigW, Ranks.r]
    omega
  obtain ⟨J, hJdef⟩ : ∃ J : ℝ ⊗[ℤ] latW D j →ₗ[ℝ] ℝ ⊗[ℤ] latW D j,
      J = θ.symm.toLinearMap ∘ₗ blk K ∘ₗ θ.toLinearMap := ⟨_, rfl⟩
  have hJ : ∀ x, thW D j (J x) = blk K (thW D j x) := by
    intro x
    rw [← hθ, ← hθ, hJdef, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  ·
    intro x
    apply θ.injective
    rw [hθ, hθ, hJ, hJ, map_neg]
    funext τ
    simp only [blk_apply, hK1, Pi.neg_apply]
  ·
    intro x y
    rw [efR_formula, efR_formula]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [hJ, hJ, blk_apply, blk_apply, hK2]
  ·
    intro x hx
    rw [efR_formula]
    have hu : thW D j x ≠ 0 := by
      intro h0
      apply hx
      apply θ.injective
      rw [hθ, h0, map_zero]
    obtain ⟨τ0, hτ0⟩ := Function.ne_iff.1 hu
    have hterm : ∀ τ : cmTypeOfSqrt D, 0 ≤ 2 * (((((1 : ℤ) : ℤ) : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0) *
          (star (thW D j (J x) τ) ⬝ᵥ (GW D j τ *ᵥ thW D j x τ))).re ∧
        (thW D j x τ ≠ 0 → 0 < 2 * (((((1 : ℤ) : ℤ) : ℂ) * (τ : D.host.E →+* ℂ) D.host.xi0) *
          (star (thW D j (J x) τ) ⬝ᵥ (GW D j τ *ᵥ thW D j x τ))).re) := by
      intro τ
      rw [hJ, blk_apply]
      exact term_pos _ (hc τ) (K τ) (GW D j τ) (hK3 τ) (thW D j x τ)
    exact Finset.sum_pos' (fun τ _ => (hterm τ).1) ⟨τ0, Finset.mem_univ _, (hterm τ0).2 hτ0⟩
  ·
    intro a A t hA ht
    have hA' : ∀ z, θ (A z) = AW D j a (θ z) := fun z =>
      (hθ (A z)).trans ((thW_AW D j a A hA z).trans (congrArg (AW D j a) (hθ z).symm))
    have hJ' : ∀ z, θ (J z) = blk K (θ z) := fun z =>
      (hθ (J z)).trans ((hJ z).trans (congrArg (blk K) (hθ z).symm))
    have hconjA : θ.conj A = AW D j a := by
      apply LinearMap.ext
      intro u
      rw [LinearEquiv.conj_apply_apply, hA', LinearEquiv.apply_symm_apply]
    have hconjJA : θ.conj (J ∘ₗ A) = blk K ∘ₗ AW D j a := by
      apply LinearMap.ext
      intro u
      rw [LinearEquiv.conj_apply_apply, LinearMap.comp_apply, hJ', hA', LinearEquiv.apply_symm_apply,
        LinearMap.comp_apply]
    have hcomm' : J ∘ₗ A = A ∘ₗ J := by
      apply LinearMap.ext
      intro z
      apply θ.injective
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hJ', hA', hA', hJ']
      exact LinearMap.congr_fun (AW_comm D j a K) (θ z)
    have htrA : LinearMap.trace ℝ _ A = LinearMap.trace ℝ _ (AW D j a) := by
      rw [← hconjA, LinearMap.trace_conj']
    have htrJA : LinearMap.trace ℝ _ (J ∘ₗ A) = LinearMap.trace ℝ _ (blk K ∘ₗ AW D j a) := by
      rw [← hconjJA, LinearMap.trace_conj']
    rw [sum_filter_eq_sum_cm_type D] at ht
    subst ht
    refine ⟨?_, ?_, ?_⟩
    · exact hcomm'
    · rw [htrA, trace_AW, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [hr]
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.conj_re,
        Complex.conj_im]
      push_cast
      ring
    · rw [htrJA, trace_K_AW, Complex.im_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [hK4]
      simp only [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
        Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im]
      ring

theorem sgnW_eq_one (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) : sgnW D j = 1 := by
  unfold sgnW
  rw [if_pos ⟨datInt_holds D j, by simpa using domFor_one D j hj (datInt_holds D j)⟩]

end Sign

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem latHat_eq_hat (V : HSp D) : latHat V = GlobalTheory.AdLat.hat D.host.F (latC V : Set (Fin V.rank → D.host.E)) := by
  unfold latHat GlobalTheory.AdLat.hat
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, V.frame.equivFun x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, ha, x, hx, rfl⟩

theorem latC_fg (V : HSp D) : (latC V).FG := V.standardTuple_isLattice.fg.map _

theorem latC_span (V : HSp D) : Submodule.span D.host.E (latC V : Set (Fin V.rank → D.host.E)) = ⊤ := by
  have h := V.standardTuple_isLattice.span_eq_top
  have : (latC V : Set (Fin V.rank → D.host.E)) =
      (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)) '' (V.L0 : Set V.V) := rfl
  rw [this, ← Submodule.map_span, h, Submodule.map_top, LinearEquiv.range]

theorem finVec_mem_gLat_one (V : HSp D) (v : Fin V.rank → D.host.E) : finVec V v ∈ gLat V 1 ↔ v ∈ latC V := by
  have h := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank (latC V) (latC_fg V) (latC_span V)).1 v
  rw [← h, ← latHat_eq_hat]
  unfold gLat
  rw [map_one]
  constructor
  · rintro ⟨z, hz, e⟩
    have e' : z = finVec V v := by simpa using e
    rw [e'] at hz
    exact hz
  · intro hz
    exact ⟨finVec V v, hz, by simp⟩

def iotaW (D : D7) (j : ℕ) : latW D j →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E) :=
  (((D.sp.W j).frame.equivFun : (D.sp.W j).V →ₗ[D.host.E] (Fin (D.sp.W j).rank → D.host.E)).restrictScalars
    (𝓞 D.host.E)) ∘ₗ (latW D j).subtype

theorem iotaOK_at_lift (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) :
    IotaOK (datumW D j hj) (D.sp.W j) (iotaW D j) where
  rt := rfl
  rt0 := rfl
  emb := by
    refine ⟨(D.sp.W j).frame.equivFun.injective.comp Subtype.val_injective, ?_⟩
    show LinearMap.range (iotaW D j) = _
    unfold iotaW latG
    rw [LinearMap.range_comp, Submodule.range_subtype, latW, Submodule.map_span]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, (D.sp.W j).frame.equivFun x, (finVec_mem_gLat_one _ _).2 ⟨x, hx, rfl⟩,
        map_smul (D.sp.W j).frame.equivFun a x⟩
    · rintro ⟨a, ha, v, hv, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (finVec_mem_gLat_one _ _).1 hv
      exact ⟨a • x, ⟨a, ha, x, hx, rfl⟩, map_smul (D.sp.W j).frame.equivFun a x⟩
  isom := fun x y => by
    have e : ∀ x : latW D j, (D.sp.W j).frame.equivFun.symm (iotaW D j x) = (x : (D.sp.W j).V) :=
      fun x => (D.sp.W j).frame.equivFun.symm_apply_apply _
    show ((sgnW D j * intForm (efQ D j) (datInt_holds D j) x y : ℤ) : ℚ) = _
    rw [sgnW_eq_one D j hj, _root_.one_mul]
    refine (intForm_cast (efQ D j) (datInt_holds D j) x y).trans ?_
    erw [e, e]
    rfl

theorem hT_coord (V : HSp D) (x y : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm y) (V.frame.equivFun.symm x) = -herm (-V.gramᵀ) x y := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul,
    herm, Matrix.neg_apply, Matrix.transpose_apply, smul_eq_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  show x a * (cc (y b) * V.gram b a) = _
  ring

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  have h : V.frame.equivFun.symm v = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    rw [← V.frame.equivFun.symm_apply_apply x, hT_coord, herm, Finset.sum_comm, neg_eq_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul]
    have := congrFun hz b
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    have e : ∑ a, v a * (-V.gramᵀ) a b = -∑ a, V.gram b a * v a := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun a _ => by simp [mul_comm]
    rw [e, this, neg_zero, zero_mul]
  exact V.frame.equivFun.symm.map_eq_zero_iff.1 h

theorem latG_one_span (V : HSp D) : Submodule.span D.host.E (latG V 1 : Set (Fin V.rank → D.host.E)) = ⊤ := by
  have hA : D.host.AA ≠ 0 := by
    intro h
    have := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h, mul_zero, zero_mul, zero_mul] at this
    exact zero_ne_one this
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ D.host.AA, a ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hA (FractionalIdeal.eq_zero_iff.2 hc)
  rw [eq_top_iff, ← latC_span V, Submodule.span_le]
  intro v hv
  have : v = a⁻¹ • (a • v) := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (Submodule.subset_span ⟨a, ha, v, (finVec_mem_gLat_one V v).2 hv, rfl⟩))

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem isom_model {V : HSp D} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (h : IotaOK Dw V ι) (x y : Dw.La) :
    ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (ι x) (ι y)) := by
  have halt : Dw.EF x y = -Dw.EF y x := by
    have := Dw.alt (x + y)
    simp only [map_add, LinearMap.add_apply, Dw.alt] at this
    linarith
  rw [halt, Int.cast_neg, h.isom, hT_coord, neg_neg, mul_neg, map_neg, neg_neg]

theorem exists_ctx_ok (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ)
    (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : IotaOK Dw V ι) (hpq : 1 ≤ Dw.p + Dw.q)
    (hA : l.A = 1) (hσ : GoodEmb c σ) : ∃ C : Ctx Xo c σ V V.rank, C.OK ∧ C.ι = ι := by
  classical
  let e : Fin (Fintype.card (Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good D.host.E H l c σ hσ).2.2.2 Dw _ e
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws D.host.E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => relab c σ (e j).1) hpq hσ hty
  obtain ⟨M, hB, -, hM⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt D.host.E H Dw l Xo _ _ _ F V.rank (-D.host.xi0)
    (-V.gramᵀ) ι (by show IsCMField.complexConj D.host.E (-D.host.xi0) = _; rw [map_neg, conj_xi0_alt])
    (fun τ hτ => by
      rw [hι.rt, hι.rt0] at hτ
      have h1 := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
      rw [if_pos (sqrt_im_pos D), Int.cast_one, _root_.one_mul] at h1
      rw [map_neg, Complex.neg_im]
      linarith)
    ⟨hι.emb.1, by rw [← latG_one_span V, ← hι.emb.2]; rfl,
      fun a b => by
        have hh : IsCMField.complexConj D.host.E (V.hT (V.frame b) (V.frame a)) = V.hT (V.frame a) (V.frame b) :=
          LinearMap.isSymm_def.1 V.herm _ _
        show IsCMField.complexConj D.host.E (-V.hT (V.frame b) (V.frame a)) = -V.hT (V.frame a) (V.frame b)
        rw [map_neg, hh],
      by
        rw [Matrix.det_neg, Matrix.det_transpose]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (gram_det_ne V),
      isom_model hι⟩
  choose θ hθ using GlobalTheory.RecModel.exists_isInfEmb D
  let k₀ : Fin F.n := ⟨0, F.n_pos⟩
  let x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun τ => if h : τ ∈ (M.X k₀).Ψ then ((M.X k₀).signature ⟨τ, h⟩).choose else 1
  refine ⟨⟨rfl, _, e, F, M, ι, θ, x₀⟩, ⟨hι, hpq, hA, hσ, hB, fun k => ⟨(hM k).1, (hM k).2⟩, hθ, fun k τ hτ => ?_⟩, rfl⟩
  have h0 : τ ∈ (M.X k₀).Ψ := ((hB.type k₀).2 τ).2 (((hB.type k).2 τ).1 hτ)
  have := ((M.X k₀).signature ⟨τ, h0⟩).choose_spec.2
  show gram τ (M.X k).Gm (x₀ τ) = Matrix.diagonal fun a : Fin V.rank => ((sgn (M.X k).p0 (a : ℕ) : ℝ) : ℂ)
  rw [(hM k).1, ← (hM k₀).1, (hB.type k).1, ← (hB.type k₀).1]
  simp only [x₀, dif_pos h0]
  exact this

theorem exists_ctx_ok_at_lift (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) :
    ∃ (l : Level (hostOfRecord D)) (Xo : Moduli (datumW D j hj) l) (c : Coeff l) (σ : c.F →+* ℂ)
      (C : Ctx Xo c σ (D.sp.W j) (D.sp.W j).rank), C.OK ∧ 3 ≤ (D.sp.W j).rank ∧ 0 < C.F.n ∧
        l.M = D.host.g 0 * D.host.g 1 := by
  have hm := D.R.m_add_three_le_k
  have hpq : 1 ≤ (datumW D j hj).p + (datumW D j hj).q := by
    show 1 ≤ (D.R.sigW j).1 + (D.R.sigW j).2
    simp only [Ranks.sigW]
    omega
  let l : Level (hostOfRecord D) := levelG D
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists D.host.E (hostOfRecord D) (datumW D j hj) l hpq
  obtain ⟨c, -⟩ := GlobalTheory.exists_coeff_containing D.host.E (hostOfRecord D) l ∅ (by simp)
  obtain ⟨C, hC, -⟩ := exists_ctx_ok Xo c c.F.val.toRingHom (D.sp.W j) (iotaW D j) (iotaOK_at_lift D j hj) hpq
    (levelG_M D _).2 rfl
  refine ⟨l, Xo, c, _, C, hC, ?_, C.F.n_pos, (levelG_M D _).1⟩
  have := hC.base.rank
  change _ = (D.R.sigW j).1 + (D.R.sigW j).2 at this
  simp only [Ranks.sigW] at this
  omega

end GlobalTheory.Member.Inhab
