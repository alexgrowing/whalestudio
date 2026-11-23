import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import Development.AutomorphicArithmetic.WhittakerHecke.LintegralIdeleRatPolyDecayMulNormRpowLtTop
import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re (x : A ℚ) : |re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

private theorem re_mul (x y : A ℚ) : re (x * y) = re x * re y := by
  simp [re]

private theorem re_add (x y : A ℚ) : re (x + y) = re x + re y := by
  simp [re]

private theorem re_congr {x y : A ℚ} (h : x.1 = y.1) : re x = re y := by
  unfold re
  have : TR.pInf ℚ x = TR.pInf ℚ y := by
    change (TR.infEq ℚ).symm x.1 = (TR.infEq ℚ).symm y.1
    rw [h]
  rw [this]

private theorem re_one : re (1 : A ℚ) = 1 := by
  simp [re]

private theorem row_sq {k : G1 ℚ} (hk : InfOrth k) :
    re (k 1 0) ^ 2 + re (k 1 1) ^ 2 = 1 := by
  have h := re_congr (hk 1 1)
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  rw [re_add, re_mul, re_mul, re_one] at h
  nlinarith [h]

private theorem abs_re_le_infPart (x : Fin 2 → A ℚ) (j : Fin 2) : |re (x j)| ≤ ‖infPartPi x‖ := by
  rw [abs_re]
  exact (GroundTheory.Automorphic.GJGlobal.norm_apply_le_norm_homeomorphMixedSpace _ _).trans
    (norm_le_pi_norm (infPartPi x) j)

private theorem abs_re_le {k : G1 ℚ} (hk : InfOrth k) (z : A ℚ) :
    |re z| ≤ 2 * ‖infPartPi fun j => z * row k j‖ := by
  set N := ‖infPartPi fun j => z * row k j‖ with hN
  have h0 : |re z| * |re (k 1 0)| ≤ N := by
    have h : |re (z * k 1 0)| ≤ N := abs_re_le_infPart (fun j => z * row k j) 0
    rwa [re_mul, abs_mul] at h
  have h1 : |re z| * |re (k 1 1)| ≤ N := by
    have h : |re (z * k 1 1)| ≤ N := abs_re_le_infPart (fun j => z * row k j) 1
    rwa [re_mul, abs_mul] at h
  have hs := row_sq hk
  have hz := abs_nonneg (re z)
  have ha := abs_nonneg (re (k 1 0))
  have hb := abs_nonneg (re (k 1 1))
  have hs' : |re (k 1 0)| ^ 2 + |re (k 1 1)| ^ 2 = 1 := by simpa [sq_abs] using hs
  by_contra hc
  push_neg at hc
  have hlt : |re (k 1 0)| + |re (k 1 1)| ≥ 1 := by nlinarith
  nlinarith

private theorem fin_eq {k : G1 ℚ} (z : A ℚ) :
    z.2 = (z * row k 0).2 * (-(k 0 1).2) + (z * row k 1).2 * (k 0 0).2 := by
  have hd := congrArg Prod.snd k.det_coe
  rw [Matrix.det_fin_two] at hd
  have hd' : (k 0 0).2 * (k 1 1).2 - (k 0 1).2 * (k 1 0).2 = 1 := hd
  change z.2 = (z.2 * (k 1 0).2) * (-(k 0 1).2) + (z.2 * (k 1 1).2) * (k 0 0).2
  linear_combination (-z.2) * hd'

theorem UpperTheory.schwartzBruhat_row_lintegral_abs_pow_bounded :
    ∀ Φ ∈ schwartzBruhatPi ℚ (Fin 2), ∀ e : ℝ, 1 < e → ∃ C : ℝ≥0, ∀ k ∈ KK ℚ,
        ∫⁻ z : IdeleGroup ℚ, ‖Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j‖ₑ * ENNReal.ofReal (ab z ^ e) ∂(ideleMeasure ℚ) ≤ C := by
  intro Φ hΦ e he
  obtain ⟨M, hM⟩ := exists_nat_gt e
  obtain ⟨C₀, hC₀, L, hL, hmaj⟩ := GroundTheory.Automorphic.GJGlobal.exists_majorant_pi hΦ M
  set O : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) := ↑(integralFiniteAdeles (𝓞 ℚ) ℚ) with hO
  have hOc : IsCompact O := isCompact_integralFiniteAdeles ℚ
  set K' : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × FiniteAdeleRing (𝓞 ℚ) ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ =>
      p.1 0 * p.2.1 + p.1 1 * p.2.2) '' (L ×ˢ (O ×ˢ O)) with hK'
  have hK'c : IsCompact K' := (hL.prod (hOc.prod hOc)).image (by fun_prop)
  have hI := UpperTheory.lintegral_idele_rat_polyDecay_mul_norm_rpow_lt_top K' hK'c e he M hM
  set I : ℝ≥0∞ := ∫⁻ y : IdeleGroup ℚ, (if (y : A ℚ).2 ∈ K' then
    ENNReal.ofReal (((1 + |re (y : A ℚ)|) ^ M)⁻¹ * ab y ^ e) else 0) ∂(ideleMeasure ℚ) with hIdef
  refine ⟨(ENNReal.ofReal (C₀ * 2 ^ M) * I).toNNReal, fun k hk => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne), hIdef,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  have hab : 0 ≤ ab z ^ e := by
    have : 0 < ab z := (IdeleGroup.ideleModule ℚ z).2
    positivity
  set x : Fin 2 → A ℚ := fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j with hx
  have hm := hmaj x
  by_cases hxL : finPartPi x ∈ L
  · rw [Set.indicator_of_mem hxL, mul_one] at hm
    have hmem : ((z : (A ℚ)ˣ) : A ℚ).2 ∈ K' := by
      refine ⟨(finPartPi x, -(k 0 1).2, (k 0 0).2), ⟨hxL, ?_, ?_⟩, (fin_eq _).symm⟩
      · exact Subring.neg_mem _ (mem_integralFiniteAdeles.2 fun v => hk.2 v 0 1)
      · exact mem_integralFiniteAdeles.2 fun v => hk.2 v 0 0
    rw [if_pos hmem, ← ENNReal.ofReal_mul (by positivity)]
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle := abs_re_le hk.1 ((z : (A ℚ)ˣ) : A ℚ)
    set N := ‖infPartPi x‖ with hN
    have hN0 : 0 ≤ N := norm_nonneg _
    have hpow : (1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M ≤ 2 ^ M * (1 + N) ^ M := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) M
    have hinv : ((1 + N) ^ M)⁻¹ ≤ 2 ^ M * ((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹ := by
      rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv, inv_mul_le_iff₀ (by positivity)]
      exact hpow
    calc ‖Φ x‖ * ab z ^ e ≤ (C₀ * ((1 + N) ^ M)⁻¹) * ab z ^ e :=
          mul_le_mul_of_nonneg_right hm hab
      _ ≤ (C₀ * (2 ^ M * ((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹)) * ab z ^ e :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hC₀) hab
      _ = C₀ * 2 ^ M * (((1 + |re ((z : (A ℚ)ˣ) : A ℚ)|) ^ M)⁻¹ * ab z ^ e) := by ring
  · rw [Set.indicator_of_notMem hxL, mul_zero] at hm
    have h0 : Φ x = 0 := norm_le_zero_iff.1 hm
    simp [h0]
