import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NormDetDenomLeRankOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EisAutomorphyLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicitStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EmbeddingCompatibleWithWeilAndDenominatorStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.EisSiegel

variable {N : ℕ}

theorem det_growth (C D Z : Matrix (Fin N) (Fin N) ℂ) (h : D * Cᴴ = C * Dᴴ)
    (hQ : (C * Z + D).det ≠ 0) (hZ : (imH Z).PosDef) (v : Fin N → ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ (C *ᵥ v ≠ 0 → 0 < c) ∧ ∀ t : ℝ, ‖(C * Z + D).det‖ * (1 + t * c) ≤
      ‖(C * (Z + (I * t) • vecMulVec v (star v)) + D).det‖ := by
  have hH : (C * Dᴴ).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, h]
  set Q := C * Z + D with hQdef
  have hU : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ
  set x : Fin N → ℂ := (Q⁻¹)ᴴ *ᵥ v with hx
  have hxv : Qᴴ *ᵥ x = v := by
    rw [hx, mulVec_mulVec, ← conjTranspose_mul, nonsing_inv_mul _ hU, conjTranspose_one, one_mulVec]
  have hsx : star x = star v ᵥ* Q⁻¹ := by
    rw [hx, star_mulVec, conjTranspose_conjTranspose]
  have hs := im_quad_denom C D Z hH x
  rw [← hQdef, hxv] at hs
  refine ⟨(star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re,
    (Complex.nonneg_iff.1 (hZ.posSemidef.dotProduct_mulVec_nonneg (Cᴴ *ᵥ x))).1,
    fun hv => (Complex.pos_iff.1 (hZ.dotProduct_mulVec_pos fun h0 => hv ?_)).1, fun t => ?_⟩
  · rw [← hxv, hQdef, conjTranspose_add, conjTranspose_mul, add_mulVec, ← mulVec_mulVec x Zᴴ, h0,
      mulVec_zero, zero_add, mulVec_mulVec, ← h, ← mulVec_mulVec, h0, mulVec_zero]
  · have e : C * (Z + (I * t) • vecMulVec v (star v)) + D =
        Q * (1 + vecMulVec ((I * t) • (Q⁻¹ *ᵥ (C *ᵥ v))) (star v)) := by
      rw [Matrix.mul_add Q, Matrix.mul_one, mul_vecMulVec, mulVec_smul, mulVec_mulVec,
        mul_nonsing_inv _ hU, one_mulVec, Matrix.mul_add, ← smul_vecMulVec, mul_vecMulVec,
        mulVec_smul, hQdef]
      abel
    rw [e, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, norm_mul,
      dotProduct_smul, dotProduct_mulVec (star v), ← hsx]
    generalize (star (Cᴴ *ᵥ x) ⬝ᵥ imH Z *ᵥ (Cᴴ *ᵥ x)).re = c at hs
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) (Complex.re_le_norm _)) (norm_nonneg _)
    simp only [smul_eq_mul, add_re, one_re, mul_re, mul_im, I_re, I_im, zero_mul, one_mul,
      ofReal_re, ofReal_im, hs]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n : ℕ}

omit [NumberField E] [IsCMField E] in

theorem pushZ_mem {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ} (ht : 0 ≤ t) :
    pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have hP : ((t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a))).PosSemidef :=
    (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht)
  have := imH_add_I_smul (Z τ) _ hP.1
  rw [smul_smul] at this
  exact this ▸ (hZ τ).add_posSemidef hP

omit [NumberField E] [IsCMField E] in
theorem dropZ_pushZ (Z : CM Ψ (N + 1) (N + 1)) (t : ℝ) :
    dropZ Ψ (pushZ Ψ Z (Pi.single 0 1) t) = dropZ Ψ Z := by
  funext τ
  ext a b
  simp [dropZ, pushZ, vecMulVec_apply]

theorem hDen_growth {γ : M2 E N} (hγ : γ ∈ UU E N) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N)
    (v : Fin N → E) (τ : Ψ) :
    (hDen Ψ γ Z τ).det ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧ (γ.toBlocks₂₁ *ᵥ v ≠ 0 → 0 < c) ∧ ∀ t : ℝ,
      ‖(hDen Ψ γ Z τ).det‖ * (1 + t * c) ≤ ‖(hDen Ψ γ (pushZ Ψ Z v t) τ).det‖ := by
  have h0 := (((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1
  obtain ⟨c, h1, h2, h3⟩ := det_growth _ _ _ (HermComp.row_rel _ (HAct.map_mem τ.1 hγ)).2 h0
    (hZ τ) (fun a => τ.1 (v a))
  refine ⟨h0, c, h1, fun hv => h2 fun h => hv ?_, h3⟩
  funext a
  apply τ.1.injective
  rw [RingHom.map_mulVec, Pi.zero_apply, map_zero]
  exact congrFun h a

theorem norm_term_le {γ : M2 E N} (hγ : γ ∈ UU E N) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N)
    (v : Fin N → E) (φ : Matrix (Fin n) (Fin N) E → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖eisTerm Ψ γ φ (pushZ Ψ Z v t) 0 0‖ ≤ ‖eisTerm Ψ γ φ Z 0 0‖ := by
  simp only [eisTerm, EisTrans.hFac_zero, norm_mul, norm_inv, norm_prod, norm_pow]
  refine mul_le_mul_of_nonneg_left (inv_anti₀ ?_ ?_) (norm_nonneg _)
  · exact Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.2 (hDen_growth Ψ hγ hZ v τ).1) _
  · refine Finset.prod_le_prod (fun _ _ => by positivity) fun τ _ => ?_
    obtain ⟨-, c, h1, -, h3⟩ := hDen_growth Ψ hγ hZ v τ
    refine pow_le_pow_left₀ (norm_nonneg _) (le_trans ?_ (h3 t)) _
    exact le_mul_of_one_le_right (norm_nonneg _) (by nlinarith [mul_nonneg ht h1])

theorem term_tendsto_zero (hΨ : IsType Ψ) (hn : n ≠ 0) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) (hv : γ.toBlocks₂₁ *ᵥ v ≠ 0)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    Tendsto (fun t : ℝ => eisTerm Ψ γ φ (pushZ Ψ Z v t) 0 0) atTop (𝓝 0) := by
  have hne : Nonempty Ψ := by
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : σ ∈ Ψ
    · exact ⟨⟨σ, h⟩⟩
    · exact ⟨⟨_, not_not.1 ((hΨ σ).not.1 h)⟩⟩
  simp only [eisTerm, EisTrans.hFac_zero, ← Finset.prod_inv_distrib]
  have h1 : ∀ τ : Ψ, Tendsto (fun t : ℝ => ((hDen Ψ γ (pushZ Ψ Z v t) τ).det ^ n)⁻¹) atTop
      (𝓝 0) := by
    intro τ
    obtain ⟨h0, c, -, h2, h3⟩ := hDen_growth Ψ hγ hZ v τ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv, norm_pow]
    refine Tendsto.inv_tendsto_atTop ((tendsto_pow_atTop hn).comp (tendsto_atTop_mono h3 ?_))
    exact Tendsto.const_mul_atTop (norm_pos_iff.2 h0)
      (tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_mul_const (h2 hv)))
  have h2 := (tendsto_finset_prod Finset.univ fun τ _ => h1 τ).const_mul (weil Ψ γ φ 0)
  rwa [Finset.prod_const, zero_pow (Finset.card_univ.trans_ne Fintype.card_ne_zero), mul_zero] at h2

end GlobalTheory.SW.EisSiegel

open GlobalTheory.SW.EisSiegel in

theorem GlobalTheory.SW.eis_siegel_operator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → ∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → ∀ Z ∈ Hn Ψ (N + 1), Tendsto (fun t : ℝ => eis Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) 0 0) atTop (𝓝 (eis Ψ (dropF φ) (dropZ Ψ Z) 0 0)) := by
  intro E _ _ _ Ψ hΨ n N hn hN φ hφ Z hZ
  obtain ⟨ι, hι, hsurj⟩ := GlobalTheory.T.embedding_compatible_with_weil_and_denominator E Ψ hΨ n N hn
  let j : Lag E N → Lag E (N + 1) := fun V =>
    ⟨botSpan (ι V.2.choose), _, (hι _ V.2.choose_spec.1).1, rfl⟩
  have hj : Function.Injective j := fun V W h => Subtype.ext (by
    rw [← V.2.choose_spec.2, ← W.2.choose_spec.2]
    exact ((hι _ V.2.choose_spec.1).2.2.2.2 _ W.2.choose_spec.1).1 (congrArg Subtype.val h))
  unfold eis
  rw [← tsum_extend_zero hj]
  refine tendsto_tsum_of_dominated_convergence
    ((eis_automorphy_linear E Ψ hΨ n (N + 1) hn hN φ hφ Z hZ).1 0 0) (fun U => ?_) ?_
  · by_cases hU : ∃ V, j V = U
    · obtain ⟨V, rfl⟩ := hU
      rw [hj.extend_apply]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      obtain ⟨a1, -, a3, a4, -⟩ := hι _ V.2.choose_spec.1
      rw [(GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E Ψ hΨ n (N + 1) hn φ hφ).2 _ (j V).2.choose_spec.1 _ a1
        (j V).2.choose_spec.2 _ (pushZ_mem Ψ hZ _ ht)]
      simp only [eisTerm, EisTrans.hFac_zero, a3, dropZ_pushZ]
      rw [← a4 φ hφ, dropF]
      congr 2
      ext k a
      refine Fin.cases rfl (fun _ => rfl) a
    · rw [Function.extend_apply' _ _ _ hU]
      refine term_tendsto_zero Ψ hΨ (by omega) U.2.choose_spec.1 hZ _ (fun h0 => hU ?_) φ
      obtain ⟨γ, hγ, e⟩ := hsurj _ U.2.choose_spec.1 fun a => by
        simpa using congrFun h0 a
      let V : Lag E N := ⟨botSpan γ, γ, hγ, rfl⟩
      refine ⟨V, Subtype.ext ?_⟩
      rw [← U.2.choose_spec.2, e]
      exact ((hι _ V.2.choose_spec.1).2.2.2.2 _ hγ).2 V.2.choose_spec.2
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht U
    exact norm_term_le Ψ U.2.choose_spec.1 hZ _ φ ht
