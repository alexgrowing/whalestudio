import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.QuadCocycle
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicitStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaEisensteinConvergeBoundedStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PosSemidefSubSmulOne
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.EisTrans

variable {N : ℕ}

open scoped MatrixOrder in

theorem exists_sub_posSemidef {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Y.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ (Y - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨1, one_pos, by rw [Subsingleton.elim (_ - _) 0]; exact PosSemidef.zero⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff (A := Matrix (Fin N) (Fin N) ℂ)
    hY.isStrictlyPositive.isSelfAdjoint).2 fun x hx => hY.isStrictlyPositive.spectrum_pos hx
  refine ⟨r, hr, ?_⟩
  have := Matrix.le_iff.mp hle
  rwa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] at this

theorem exists_mem_HnGe {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {Z : CM Ψ N N}
    (hZ : Z ∈ Hn Ψ N) : ∃ δ : ℝ, 0 < δ ∧ Z ∈ HnGe Ψ N δ := by
  first
  | exact @_root_.GlobalTheory.PosSemidefShiftByScalar.main
  | exact _root_.GlobalTheory.PosSemidefShiftByScalar.main
  | (apply _root_.GlobalTheory.PosSemidefShiftByScalar.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PosSemidefShiftByScalar.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PosSemidefShiftByScalar.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PosSemidefShiftByScalar.main ..)

theorem entry_bound {C D Z : Matrix (Fin N) (Fin N) ℂ} {δ : ℝ} (hδ : 0 < δ)
    (h : D * Cᴴ = C * Dᴴ) (hQ : (C * Z + D).det ≠ 0)
    (hZ : (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) (i j : Fin N) :
    ‖((C * Z + D)⁻¹ * C) i j‖ ≤ δ⁻¹ := by
  have e0 : (C * Z + D) * Cᴴ - C * (C * Z + D)ᴴ = C * (Z - Zᴴ) * Cᴴ := by
    rw [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, h]; noncomm_ring
  generalize C * Z + D = Q at e0 hQ
  have hi : Q⁻¹ * Q = 1 := nonsing_inv_mul Q (Ne.isUnit hQ)
  have hi' : Qᴴ * (Q⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, hi, conjTranspose_one]
  have e1 : (Q⁻¹ * C) * (Z - Zᴴ) * (Q⁻¹ * C)ᴴ = (Q⁻¹ * C)ᴴ - Q⁻¹ * C := by
    calc _ = Q⁻¹ * (C * (Z - Zᴴ) * Cᴴ) * (Q⁻¹)ᴴ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Q⁻¹ * Q) * (Cᴴ * (Q⁻¹)ᴴ) - Q⁻¹ * C * (Qᴴ * (Q⁻¹)ᴴ) := by rw [← e0]; noncomm_ring
      _ = _ := by rw [hi, hi', conjTranspose_mul, Matrix.one_mul, Matrix.mul_one]
  generalize Q⁻¹ * C = S at e1
  have key : δ * ∑ k, ‖S i k‖ ^ 2 ≤ ‖S i i‖ := by
    have h1 := (hZ.mul_mul_conjTranspose_same S).diag_nonneg (i := i)
    rw [Matrix.mul_sub, Matrix.sub_mul, imH, Matrix.mul_smul, Matrix.smul_mul, e1,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at h1
    have h2 : (S * Sᴴ) i i = ((∑ k, ‖S i k‖ ^ 2 : ℝ) : ℂ) := by
      simp [Matrix.mul_apply, Complex.mul_conj']
    have h3 : (2 * I)⁻¹ * (conj (S i i) - S i i) = ((-(S i i).im : ℝ) : ℂ) := by
      rw [← neg_sub, Complex.sub_conj]; push_cast; field_simp
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, h2, conjTranspose_apply,
      Complex.star_def, h3] at h1
    have h4 : (0 : ℝ) ≤ -(S i i).im - δ * ∑ k, ‖S i k‖ ^ 2 := by exact_mod_cast h1
    have h5 := (abs_le.1 (Complex.abs_im_le_norm (S i i))).1
    linarith
  have hs : ∀ k, δ * ‖S i k‖ ^ 2 ≤ ‖S i i‖ := fun k => le_trans (mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := fun k => ‖S i k‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ k)) hδ.le) key
  have a1 : δ * ‖S i i‖ ≤ 1 := by
    by_contra hc
    push Not at hc
    have : 0 < ‖S i i‖ := by by_contra h0; nlinarith [norm_nonneg (S i i)]
    nlinarith [hs i]
  rw [← one_div, le_div_iff₀ hδ]
  by_contra hc
  push Not at hc
  nlinarith [hs j, mul_le_mul_of_nonneg_left (hs j) hδ.le]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n : ℕ}

omit [NumberField E] [IsCMField E] in

theorem hFac_zero (γ : M2 E N) (Z : CM Ψ N N) :
    hFac Ψ γ Z (0 : CM Ψ n N) 0 = ∏ τ : Ψ, (hDen Ψ γ Z τ).det ^ n := by
  unfold hFac
  have h : ∀ (τ : Ψ) (k : Fin n), (0 : CM Ψ n N) τ k = 0 := fun _ _ => rfl
  simp only [h, zero_dotProduct]
  simp

theorem hFac_inv_bound {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (z z' : CM Ψ n N) :
    ∃ K : ℝ, ∀ γ ∈ UU E N,
      ‖(hFac Ψ γ Z z z')⁻¹‖ ≤ K * ‖(hFac Ψ γ Z (0 : CM Ψ n N) 0)⁻¹‖ := by
  obtain ⟨δ, hδ, hZ'⟩ := exists_mem_HnGe Ψ hZ
  refine ⟨∏ τ : Ψ, Real.exp (‖2 * (π : ℂ) * I‖ * ∑ k, ∑ a, ‖z' τ k a‖ * ∑ b, δ⁻¹ * ‖z τ k b‖),
    fun γ hγ => ?_⟩
  rw [hFac_zero, hFac, Finset.prod_mul_distrib, mul_inv, norm_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [← Finset.prod_inv_distrib, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  rw [← Complex.exp_neg]
  refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
  rw [norm_neg, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hb := entry_bound hδ (HermComp.row_rel _ (HAct.map_mem τ.1 hγ)).2
    (((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).1 τ).1 (hZ' τ)
  refine norm_sum_le_of_le _ fun k _ => norm_sum_le_of_le _ fun a _ => ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [Matrix.mulVec, dotProduct]
  refine norm_sum_le_of_le _ fun b _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hb a b) (norm_nonneg _)

omit [NumberField E] [IsCMField E] in

theorem botSpan_mul (g γ : M2 E N) : botSpan (g * γ) = (botSpan g).map γ.vecMulLinear := by
  unfold botSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

noncomputable def lagMul {γ : M2 E N} (hγ : γ ∈ UU E N) (U : Lag E N) : Lag E N :=
  ⟨U.1.map γ.vecMulLinear, U.2.choose * γ, HAct.mul_mem hγ U.2.choose_spec.1, by
    rw [botSpan_mul, U.2.choose_spec.2]⟩

theorem lagMul_lagMul {γ γ' : M2 E N} (hγ : γ ∈ UU E N) (hγ' : γ' ∈ UU E N) (h : γ * γ' = 1)
    (U : Lag E N) : lagMul hγ' (lagMul hγ U) = U := by
  apply Subtype.ext
  change (U.1.map γ.vecMulLinear).map γ'.vecMulLinear = U.1
  rw [← U.2.choose_spec.2, ← botSpan_mul, ← botSpan_mul, Matrix.mul_assoc, h, Matrix.mul_one]

noncomputable def lagEquiv {γ : M2 E N} (hγ : γ ∈ UU E N) : Lag E N ≃ Lag E N :=
  ⟨lagMul hγ, lagMul (HAct.group_part hγ).2.1,
    lagMul_lagMul _ _ (mul_nonsing_inv γ (HAct.group_part hγ).1),
    lagMul_lagMul _ _ (nonsing_inv_mul γ (HAct.group_part hγ).1)⟩

end GlobalTheory.SW.EisTrans

open GlobalTheory.SW.EisTrans in

theorem GlobalTheory.SW.eis_automorphy_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → ∀ Z ∈ Hn Ψ N, (∀ z z', Summable fun U : Lag E N => ‖eisTerm Ψ U.2.choose φ Z z z'‖) ∧ (∀ γ ∈ UU E N, eis Ψ (weil Ψ γ φ) (hAct Ψ γ Z) 0 0 = hFac Ψ γ Z (0 : CM Ψ n N) 0 * eis Ψ φ Z 0 0) ∧ (∀ ψ, IsSB ψ → ∀ z z', eis Ψ (φ + ψ) Z z z' = eis Ψ φ Z z z' + eis Ψ ψ Z z z') ∧ ∀ (c : ℂ) z z', eis Ψ (c • φ) Z z z' = c * eis Ψ φ Z z z' := by
  intro E _ _ _ Ψ hΨ n N hn hN
  have hs : ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → ∀ Z ∈ Hn Ψ N, ∀ z z',
      Summable fun U : Lag E N => ‖eisTerm Ψ U.2.choose φ Z z z'‖ := by
    rintro φ ⟨R, hR, hφ⟩ Z hZ z z'
    obtain ⟨δ, hδ, hZ'⟩ := exists_mem_HnGe Ψ hZ
    obtain ⟨B, hB⟩ := (GlobalTheory.T.schwartzBruhatInnerProduct_self_nonneg_bounds E _ _ R φ hR hφ).2.2.2.2.1
    obtain ⟨C, hC⟩ := GlobalTheory.T.hermitianTheta_eisenstein_converge_bounded E Ψ hΨ n N hn hN R δ hR hδ
    obtain ⟨K, hK⟩ := hFac_inv_bound Ψ hZ z z'
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun U => ?_)
      ((hC φ hφ B hB Z hZ').1.mul_left K)
    rw [eisTerm, eisTerm, norm_mul, norm_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hK _ U.2.choose_spec.1) (norm_nonneg _)
  intro φ hφ Z hZ
  refine ⟨hs φ hφ Z hZ, fun γ hγ => ?_, fun ψ hψ z z' => ?_, fun c z z' => ?_⟩
  · unfold eis
    rw [← (lagEquiv hγ).tsum_eq (fun U => eisTerm Ψ U.2.choose φ Z 0 0), ← tsum_mul_left]
    refine tsum_congr fun U => ?_
    have hg := U.2.choose_spec.1
    rw [(GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E Ψ hΨ n N hn φ hφ).2 _ (lagEquiv hγ U).2.choose_spec.1 _
      (HAct.mul_mem hγ hg) (by
        rw [(lagEquiv hγ U).2.choose_spec.2, botSpan_mul, U.2.choose_spec.2]; rfl) Z hZ]
    have ha := (unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
    have h0 : hFac Ψ γ Z (0 : CM Ψ n N) 0 ≠ 0 := by
      rw [hFac_zero]
      exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (ha.1 τ).1
    have h1 : hFac Ψ (U.2.choose * γ) Z (0 : CM Ψ n N) 0 =
        hFac Ψ U.2.choose (hAct Ψ γ Z) (0 : CM Ψ n N) 0 * hFac Ψ γ Z (0 : CM Ψ n N) 0 := by
      simp only [hFac_zero, (ha.2.2.2 _ hg).2.1, det_mul, mul_pow, Finset.prod_mul_distrib]
    rw [eisTerm, eisTerm, h1, (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ φ hφ).2.2.2.2.2.1 _ hg, mul_inv]
    field_simp
  · unfold eis
    rw [← (hs φ hφ Z hZ z z').of_norm.tsum_add (hs ψ hψ Z hZ z z').of_norm]
    refine tsum_congr fun U => ?_
    rw [eisTerm, eisTerm, eisTerm,
      ((GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn _ U.2.choose_spec.1 φ hφ).2.2.2.1 ψ hψ).2, Pi.add_apply, add_mul]
  · unfold eis
    rw [← tsum_mul_left]
    refine tsum_congr fun U => ?_
    rw [eisTerm, eisTerm, (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn _ U.2.choose_spec.1 φ hφ).2.2.2.2.1 c,
      Pi.smul_apply, smul_eq_mul, mul_assoc]
