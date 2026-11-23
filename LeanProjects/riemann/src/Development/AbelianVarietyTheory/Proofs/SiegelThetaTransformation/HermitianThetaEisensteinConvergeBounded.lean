import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFnStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicitStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionLevelSupNormUniformInLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LinearIndependentMul
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PosSemidefSubMulConjTranspose
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableEisMajorantStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.EisBdd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

omit [IsCMField E] in

theorem approx_entry (hΨ : IsType Ψ) : ∃ K : ℝ, ∀ w : Ψ → ℂ, ∃ a : E, IsIntegral ℤ a ∧
    ∀ τ : Ψ, ‖w τ - τ.1 a‖ ≤ K := by
  classical
  refine ⟨∑ σ : E →+* ℂ, ∑ i, ‖σ (integralBasis E i)‖, fun w => ?_⟩
  let w' : (E →+* ℂ) → ℂ := fun σ => if h : σ ∈ Ψ then w ⟨σ, h⟩ else 0
  let x : (E →+* ℂ) → ℂ := fun σ => w' σ + conj (w' (ComplexEmbedding.conjugate σ))
  let c := (canonicalEmbedding.latticeBasis E).repr x
  have hx : ∀ σ, x σ = ∑ i, c i * σ (integralBasis E i) := fun σ => by
    conv_lhs => rw [← (canonicalEmbedding.latticeBasis E).sum_repr x]
    simp [c, canonicalEmbedding.latticeBasis_apply, Finset.sum_apply]
  have hre : ∀ τ : Ψ, w τ = ∑ i, ((c i).re : ℂ) * τ.1 (integralBasis E i) := fun τ => by
    have h0 : w' (ComplexEmbedding.conjugate τ.1) = 0 := dif_neg ((hΨ τ.1).1 τ.2)
    have h1 : w' τ.1 = w τ := dif_pos τ.2
    have h2 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ.1) = τ.1 := star_star _
    have e1 := hx τ.1
    have e2 := congrArg conj (hx (ComplexEmbedding.conjugate τ.1))
    simp only [x, h0, h1, h2, map_zero, add_zero, zero_add, conj_conj, map_sum, map_mul,
      ComplexEmbedding.conjugate_coe_eq] at e1 e2
    have : w τ = (w τ + w τ) / 2 := by ring
    rw [this]
    nth_rewrite 1 [e1]
    rw [e2, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_eq_add_conj]
    ring
  refine ⟨∑ i, (⌊(c i).re⌋ : E) * integralBasis E i, IsIntegral.sum _ fun i _ => ?_, fun τ => ?_⟩
  · refine IsIntegral.mul ?_ ?_
    · simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := ⌊(c i).re⌋)
    · rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
  · rw [hre, map_sum, ← Finset.sum_sub_distrib]
    refine le_trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
      (Finset.single_le_sum (f := fun σ : E →+* ℂ => ∑ i, ‖σ (integralBasis E i)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ.1))
    rw [map_mul, map_intCast, ← sub_mul, norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le

theorem approx_herm (hΨ : IsType Ψ) : ∃ K : ℝ, ∀ Z : CM Ψ N N,
    ∃ β : Matrix (Fin N) (Fin N) E, ccT β = β ∧ IntM β ∧
      ∀ (τ : Ψ) a b, ‖((Z τ - β.map τ.1) + (Z τ - β.map τ.1)ᴴ) a b‖ ≤ K := by
  obtain ⟨K, hK⟩ := approx_entry hΨ
  refine ⟨4 * K, fun Z => ?_⟩
  choose y hy hyK using fun a b : Fin N => hK fun τ => (Z τ a b + conj (Z τ b a)) / 4
  refine ⟨Matrix.of fun a b => y a b + cc (y b a), ?_, fun a b => (hy a b).add
    (Base.isIntegral_cc (hy b a)), fun τ a b => ?_⟩
  · ext a b; simp [ccT, cc, add_comm]
  · have e : ((Z τ - (Matrix.of fun a b => y a b + cc (y b a)).map τ.1) +
        (Z τ - (Matrix.of fun a b => y a b + cc (y b a)).map τ.1)ᴴ) a b =
        2 * ((Z τ a b + conj (Z τ b a)) / 4 - τ.1 (y a b)) +
        2 * conj ((Z τ b a + conj (Z τ a b)) / 4 - τ.1 (y b a)) := by
      simp [Base.map_cc, Matrix.conjTranspose_apply, map_ofNat]
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_two]
    linarith [hyK a b τ, hyK b a τ]

theorem im_nonneg {W : Matrix (Fin N) (Fin N) ℂ} (h : (imH W).PosSemidef) (v : Fin N → ℂ) :
    0 ≤ (v ⬝ᵥ W *ᵥ star v).im := by
  have h1 := h.re_dotProduct_nonneg (star v)
  have h2 : v ⬝ᵥ Wᴴ *ᵥ star v = conj (v ⬝ᵥ W *ᵥ star v) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, conjTranspose_apply, map_sum, map_mul,
      Pi.star_apply, Complex.star_def, conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [star_star, imH, smul_mulVec, sub_mulVec, dotProduct_smul, dotProduct_sub, h2,
    Complex.sub_conj, smul_eq_mul] at h1
  have h3 : (2 * I)⁻¹ * (((2 * (v ⬝ᵥ W *ᵥ star v).im : ℝ) : ℂ) * I) =
      ((v ⬝ᵥ W *ᵥ star v).im : ℂ) := by
    push_cast; field_simp
  rw [h3] at h1
  simpa using h1

theorem imH_scalar (δ : ℝ) : imH ((I * δ) • (1 : Matrix (Fin N) (Fin N) ℂ)) =
    (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  unfold imH
  rw [conjTranspose_smul, conjTranspose_one, ← sub_smul, smul_smul]
  congr 1
  simp only [Complex.star_def, map_mul, conj_I, conj_ofReal]
  field_simp
  ring

theorem imH_sub (A B : Matrix (Fin N) (Fin N) ℂ) : imH (A - B) = imH A - imH B := by
  unfold imH
  rw [← smul_sub, conjTranspose_sub]
  congr 1
  abel

theorem posDef_scalar {δ : ℝ} (hδ : 0 < δ) :
    ((δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast hδ)

omit [NumberField E] [IsCMField E] in
theorem mem_Hn {δ : ℝ} (hδ : 0 < δ) {Z : CM Ψ N N} (hZ : Z ∈ HnGe Ψ N δ) : Z ∈ Hn Ψ N := fun τ => by
  simpa using (posDef_scalar hδ).add_posSemidef (hZ τ)

open Classical in

theorem theta_bdd (hΨ : IsType Ψ) {R : ℕ} {δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, HasLevel R φ → ∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) →
      ∀ Z ∈ HnGe Ψ N δ, ‖thH Ψ φ Z 0 0‖ ≤ C * B := by
  let φ₀ : Matrix (Fin n) (Fin N) E → ℂ := fun x => if IntM ((R : E) • x) then 1 else 0
  have c : ∀ k : ℕ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
  have h₀ : IsSB φ₀ := by
    refine ⟨R, hR, fun x hx => by_contra fun h => hx (if_neg h), fun x y hy => ?_⟩
    refine if_congr (forall_congr' fun k => forall_congr' fun a => ?_) rfl rfl
    have hz : IsIntegral ℤ ((R : E) * ((R : E) * y k a)) := (c R).mul ((c R).mul (hy k a))
    simp only [smul_add, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add]
    exact ⟨fun h => by simpa using h.sub hz, fun h => h.add hz⟩
  let Z₀ : CM Ψ N N := fun _ => (I * δ) • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hZ₀ : Z₀ ∈ Hn Ψ N := fun τ => by
    simp only [Z₀, imH_scalar]; exact posDef_scalar hδ
  have hs := (GlobalTheory.T.hermitianTheta_summable_and_determines_testFn E Ψ hΨ n N φ₀ h₀ Z₀ hZ₀).1 0 0
  refine ⟨∑' x, ‖φ₀ x * cexp (2 * π * I * expo Ψ x Z₀ 0 0)‖, fun φ hφ B hB Z hZ => ?_⟩
  rw [← tsum_mul_right]
  refine tsum_of_norm_bounded (hs.mul_right B).hasSum fun x => ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  by_cases hx : φ x = 0
  · rw [hx, zero_mul, norm_zero]; positivity
  have h1 : φ₀ x = 1 := if_pos (hφ.1 x hx)
  rw [h1, one_mul, norm_mul, mul_comm]
  refine mul_le_mul ?_ (hB x) (norm_nonneg _) (norm_nonneg _)
  rw [Complex.norm_exp, Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have h2 : (expo Ψ x Z₀ 0 0).im ≤ (expo Ψ x Z 0 0).im := by
    unfold expo
    rw [Complex.im_sum, Complex.im_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [Complex.im_sum, Complex.im_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h3 := im_nonneg (W := Z τ - Z₀ τ) (by rw [imH_sub, imH_scalar]; exact hZ τ)
      fun a => τ.1 (x k a)
    rw [sub_mulVec, dotProduct_sub, Complex.sub_im, sub_nonneg] at h3
    simp only [Complex.add_im]
    exact add_le_add_left (add_le_add_left h3 _) _
  have h4 : ∀ e : ℂ, (2 * π * I * e).re = -(2 * π * e.im) := fun e => by simp
  rw [h4, h4]
  have := Real.pi_pos
  nlinarith

theorem transl_mem {β : Matrix (Fin N) (Fin N) E} (h : ccT β = β) :
    (fromBlocks 1 β 0 1 : M2 E N) ∈ UU E N := by
  have e : ccT (fromBlocks 1 β 0 1 : M2 E N) = fromBlocks 1 0 β 1 := by
    conv_rhs => rw [← h]
    ext (i | i) (j | j) <;> by_cases hij : i = j <;>
      simp [ccT, cc, Matrix.one_apply, hij, eq_comm]
  change ccT _ * _ * _ = _
  rw [e, Matrix.J, fromBlocks_multiply, fromBlocks_multiply]
  simp

omit [NumberField E] [IsCMField E] in

theorem botSpan_mul (γ t : M2 E N) : botSpan (γ * t) = (botSpan γ).map (vecMulLinear t) := by
  unfold botSpan
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem pair {γ : M2 E N} (h : γ ∈ UU E N) (τ : Ψ) :
    (γ.toBlocks₂₁.map τ.1 * (γ.toBlocks₂₂.map τ.1)ᴴ).IsHermitian ∧
    (γ.toBlocks₂₁.map τ.1 * (γ.toBlocks₂₁.map τ.1)ᴴ +
      γ.toBlocks₂₂.map τ.1 * (γ.toBlocks₂₂.map τ.1)ᴴ).PosDef ∧
    (hDen Ψ γ (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det ≠ 0 := by
  have h1 := HAct.map_mem τ.1 (HAct.group_part h).2.2.1
  rw [HAct.map_ccT, HAct.map_blocks, fromBlocks_conjTranspose] at h1
  have h2 := (HAct.blocks h1).2.2.2
  rw [conjTranspose_conjTranspose, conjTranspose_conjTranspose] at h2
  have h3 := (((unitary_act_halfSpace E Ψ N γ h).2 _ (Base.I_mem_Hn Ψ)).1 τ).1
  refine ⟨?_, ?_, h3⟩
  · rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, h2]
  · have h4 := PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit h3)))
    refine (congrArg PosDef ?_).mp h4
    simp only [hDen, Matrix.mul_smul, Matrix.mul_one, conjTranspose_add, conjTranspose_smul,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, smul_add, smul_smul, h2, Complex.star_def,
      conj_I]
    rw [show -I * I = 1 by simp, one_smul, neg_smul]
    abel

theorem eis_bdd (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {R : ℕ} {δ : ℝ} (hR : 0 < R)
    (hδ : 0 < δ) : ∃ C : ℝ, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, HasLevel R φ → ∀ B : ℝ,
      (∀ x, ‖φ x‖ ≤ B) → ∀ Z ∈ HnGe Ψ N δ,
      (Summable fun U : Lag E N => ‖eisTerm Ψ U.2.choose φ Z 0 0‖) ∧ ‖eis Ψ φ Z 0 0‖ ≤ C * B := by
  obtain ⟨c, hc, hrep⟩ := LagRep.exists_rep_den E N
  choose rep hU hD hS using hrep
  have hm := GlobalTheory.T.summable_prod_inv_norm_det_hDen_pow E Ψ hΨ n N hN c rep hc fun U => ⟨hU U, hD U, hS U⟩
  set m : Lag E N → ℝ := fun U => ∏ τ : Ψ,
    (‖(hDen Ψ (rep U) (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det‖ ^ n)⁻¹ with hmd
  have hm0 : ∀ U, 0 ≤ m U := fun U => Finset.prod_nonneg fun _ _ => by positivity
  obtain ⟨K, hK⟩ := approx_herm (N := N) hΨ
  obtain ⟨κ, hκ, hcomp⟩ := norm_det_denom_compare N δ K hδ
  obtain ⟨R', C, -, hC⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n N hn c R hc hR
  set L : ℝ := |C| * ∏ _τ : Ψ, (κ ^ n)⁻¹ with hL
  have hL0 : 0 ≤ L := mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => by positivity)
  refine ⟨L * ∑' U, m U, fun φ hφ B hB Z hZ => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨β, hβ, hβi, hβK⟩ := hK Z
  have hβ' : ccT (-β) = -β := by
    conv_rhs => rw [← hβ]
    ext i j; simp [ccT, cc]
  have ht := transl_mem hβ
  have ht' := transl_mem hβ'
  have htt : (fromBlocks 1 β 0 1 : M2 E N) * fromBlocks 1 (-β) 0 1 = 1 := by
    rw [fromBlocks_multiply]; simp
  let σ : Lag E N → Lag E N := fun U =>
    ⟨botSpan (rep U * fromBlocks 1 β 0 1), _, HAct.mul_mem ht (hU U), rfl⟩
  have hσ : ∀ U, botSpan (rep (σ U) * fromBlocks 1 (-β) 0 1) = U.1 := fun U => by
    rw [botSpan_mul, hS]
    change (botSpan (rep U * fromBlocks 1 β 0 1)).map _ = _
    rw [← botSpan_mul, Matrix.mul_assoc, htt, Matrix.mul_one, hS]
  have hinj : Function.Injective σ := fun U V h => Subtype.ext (by rw [← hσ U, h, hσ])
  have hlev : LevelL (stdL E n) R φ :=
    ⟨fun x hx a => (Base.mem_stdL _).2 fun k => hφ.1 x hx k a,
      fun x y hy => hφ.2 x y fun k a => (Base.mem_stdL _).1 (hy a) k⟩
  have key : ∀ U : Lag E N, ‖eisTerm Ψ U.2.choose φ Z 0 0‖ ≤ L * B * m (σ U) := fun U => by
    have hγ := HAct.mul_mem ht' (hU (σ U))
    rw [(GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E Ψ hΨ n N hn φ ⟨R, hR, hφ⟩).2 _ U.2.choose_spec.1 _ hγ
      (U.2.choose_spec.2.trans (hσ U).symm) Z (mem_Hn hδ hZ)]
    have hden : Den c (rep (σ U) * fromBlocks 1 (-β) 0 1) := by
      intro i j
      rw [← Matrix.smul_mul, Matrix.mul_apply]
      refine IsIntegral.sum _ fun k _ => (hD _ i k).mul ?_
      rcases k with k | k <;> rcases j with j | j
      · by_cases h : k = j <;> simp [h, isIntegral_one, isIntegral_zero]
      · exact (hβi k j).neg
      · exact isIntegral_zero
      · by_cases h : k = j <;> simp [h, isIntegral_one, isIntegral_zero]
    have h1 := (hC 1 _ (Base.stdL_mem_Vset n 1) _ hγ hden φ hlev).2.2 B hB 0
    have h2 : ‖(hFac Ψ (rep (σ U) * fromBlocks 1 (-β) 0 1) Z (0 : CM Ψ n N) 0)⁻¹‖ ≤
        (∏ _τ : Ψ, (κ ^ n)⁻¹) * m (σ U) := by
      have h0 : ∀ (τ : Ψ) (k : Fin n), (0 : CM Ψ n N) τ k = 0 := fun _ _ => rfl
      simp only [hFac, h0, zero_dotProduct, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
        mul_one, hmd]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, norm_prod]
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
      obtain ⟨p1, p2, p3⟩ := pair (hU (σ U)) τ
      have hb : (β.map τ.1)ᴴ = β.map τ.1 := by rw [← Base.ccT_map, hβ]
      have h3 := (hcomp _ _ (Z τ - β.map τ.1) p1 p2
        (by rw [imH_sub, imH, imH, hb, sub_self, smul_zero, sub_zero]; exact hZ τ) (hβK τ)).1
      have h4 : hDen Ψ (rep (σ U) * fromBlocks 1 (-β) 0 1) Z τ =
          (rep (σ U)).toBlocks₂₁.map τ.1 * (Z τ - β.map τ.1) + (rep (σ U)).toBlocks₂₂.map τ.1 := by
        obtain ⟨-, -, m3, m4⟩ := HAct.mul_blocks τ.1 (fromBlocks 1 (-β) 0 1) (rep (σ U))
        rw [hDen, m3, m4]
        simp [Matrix.map_neg, Matrix.mul_sub]
        abel
      rw [h4, norm_inv, norm_pow, ← mul_inv, ← mul_pow]
      have p4 := norm_pos_iff.2 p3
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h3 n)
    rw [eisTerm, norm_mul]
    calc _ ≤ (|C| * B) * ((∏ _τ : Ψ, (κ ^ n)⁻¹) * m (σ U)) :=
          mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hB0)) h2
            (norm_nonneg _) (by positivity)
      _ = _ := by rw [hL]; ring
  have hs : Summable fun U => L * B * m (σ U) := (hm.comp_injective hinj).mul_left _
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) key hs, ?_⟩
  refine (tsum_of_norm_bounded hs.hasSum key).trans ?_
  rw [tsum_mul_left, mul_right_comm L _ B]
  exact mul_le_mul_of_nonneg_left (_root_.tsum_comp_le_tsum_of_inj hm hm0 hinj) (by positivity)

end GlobalTheory.SW.EisBdd

open GlobalTheory.SW.EisBdd in

theorem GlobalTheory.SW.theta_eis_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ (R : ℕ) (δ : ℝ), 0 < R → 0 < δ → ∃ C : ℝ, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, HasLevel R φ → ∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → ∀ Z ∈ HnGe Ψ N δ, (Summable fun U : Lag E N => ‖eisTerm Ψ U.2.choose φ Z 0 0‖) ∧ ‖thH Ψ φ Z 0 0‖ ≤ C * B ∧ ‖eis Ψ φ Z 0 0‖ ≤ C * B := by
  intro E _ _ _ Ψ hΨ n N hn hN R δ hR hδ
  obtain ⟨C₁, h₁⟩ := theta_bdd (n := n) (N := N) hΨ hR hδ
  obtain ⟨C₂, h₂⟩ := eis_bdd hΨ hn hN hR hδ
  refine ⟨max C₁ C₂, fun φ hφ B hB Z hZ => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  exact ⟨(h₂ φ hφ B hB Z hZ).1,
    (h₁ φ hφ B hB Z hZ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB0),
    (h₂ φ hφ B hB Z hZ).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hB0)⟩
