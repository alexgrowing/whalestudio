import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import GroundTheory.AutomorphicForms.ReductionIdele
import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re' (x : A ℚ) : |UpperTheory.ConvolutionTheory.RankTwoDescent.re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

private theorem re_mul' (a b : A ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (a * b) = UpperTheory.ConvolutionTheory.RankTwoDescent.re a * UpperTheory.ConvolutionTheory.RankTwoDescent.re b := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, map_mul, Pi.mul_apply]

private theorem re_add' (a b : A ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (a + b) = UpperTheory.ConvolutionTheory.RankTwoDescent.re a + UpperTheory.ConvolutionTheory.RankTwoDescent.re b := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, map_add, Pi.add_apply]

private theorem pInf_id' (u : (TR.Rinf ℚ)ˣ) : TR.pInf ℚ (TR.infId ℚ u).val = u.val := by
  change TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ _) = _
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  simp [h]

private theorem re_iy' {s : ℝ} (hs : s ≠ 0) : UpperTheory.ConvolutionTheory.RankTwoDescent.re (UpperTheory.ConvolutionTheory.RankTwoDescent.iy s : A ℚ) = s := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, UpperTheory.ConvolutionTheory.RankTwoDescent.iy, dif_neg hs, pInf_id']

private theorem snd_iy' {s : ℝ} (hs : s ≠ 0) : (UpperTheory.ConvolutionTheory.RankTwoDescent.iy s : A ℚ).2 = 1 := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.iy, dif_neg hs]
  change (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) - 0 + 0 = 1
  simp

theorem UpperTheory.schwartzBruhat_translate_decay_bound :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi ℚ (Fin 2) → ∀ (C : Set (GL (Fin 2) (A ℚ))), IsCompact C → ∀ N : ℕ,
        ∃ (B κ : ℝ) (L : Set (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ)), 0 ≤ B ∧ 0 < κ ∧ κ ≤ 1 ∧ IsCompact L ∧
          ∀ (t : ℝ), ∀ k ∈ C, ∀ y : Fin 2 → A ℚ,
            ‖Φ fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * (y ᵥ* k.val) j‖ ≤
                B * ((1 + κ * Real.exp t * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|)) ^ N)⁻¹ ∧
              (Φ (fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * (y ᵥ* k.val) j) ≠ 0 → (fun j => (y j).2) ∈ L) := by
  intro Φ hΦ C hC N
  obtain ⟨C0, hC0, L0, hL0, hmaj⟩ := GroundTheory.Automorphic.GJGlobal.exists_majorant_pi hΦ N
  have hinv : Continuous fun k : GL (Fin 2) (A ℚ) => (k⁻¹).val :=
    Units.continuous_val.comp continuous_inv
  have hent : ∀ i j, Continuous fun k : GL (Fin 2) (A ℚ) => (k⁻¹).val i j :=
    fun i j => hinv.matrix_elem i j
  have hnorm : ∀ i j, Continuous fun k : GL (Fin 2) (A ℚ) =>
      ‖((k⁻¹).val i j).1 Rat.infinitePlace‖ := fun i j =>
    (((continuous_apply Rat.infinitePlace).comp continuous_fst).comp (hent i j)).norm
  obtain ⟨B1, hB1⟩ := hC.exists_bound_of_continuousOn
    (f := fun k : GL (Fin 2) (A ℚ) => ∑ i, ∑ j, ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => hnorm i j).continuousOn
  have hBk0 : 0 ≤ max B1 0 := le_max_right _ _
  have hBk : ∀ k ∈ C, ∀ i j, |UpperTheory.ConvolutionTheory.RankTwoDescent.re ((k⁻¹).val i j)| ≤ max B1 0 := by
    intro k hk i j
    rw [abs_re']
    have h1 := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB1 k hk))
    refine le_trans ?_ (h1.trans (le_max_left _ _))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  generalize max B1 0 = Bk at hBk0 hBk
  have hpos : 0 < 1 + 4 * Bk := by linarith
  let f : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × GL (Fin 2) (A ℚ) → Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ :=
    fun p j => p.1 0 * ((p.2⁻¹).val 0 j).2 + p.1 1 * ((p.2⁻¹).val 1 j).2
  have hf : Continuous f := by
    refine continuous_pi fun j => ?_
    exact (((continuous_apply 0).comp continuous_fst).mul
        (continuous_snd.comp ((hent 0 j).comp continuous_snd))).add
      (((continuous_apply 1).comp continuous_fst).mul
        (continuous_snd.comp ((hent 1 j).comp continuous_snd)))
  refine ⟨C0, 1 / (1 + 4 * Bk), f '' (L0 ×ˢ C), hC0, by positivity,
    (div_le_one hpos).2 (by linarith), (hL0.prod hC).image hf, fun t k hk y => ?_⟩
  have het : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hyz : ∀ j, y j = (y ᵥ* k.val) 0 * (k⁻¹).val 0 j + (y ᵥ* k.val) 1 * (k⁻¹).val 1 j := by
    intro j
    have h : (y ᵥ* k.val) ᵥ* (k⁻¹).val = y := by
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    conv_lhs => rw [← h]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  generalize hz : y ᵥ* k.val = z at hyz ⊢
  generalize hx : (fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * z j) = x
  have hxj : ∀ j, x j = (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * z j := fun j => by rw [← hx]
  have hxT : ∀ j, Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z j)| ≤ ‖infPartPi x‖ := by
    intro j
    have e : Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z j)| = |UpperTheory.ConvolutionTheory.RankTwoDescent.re (x j)| := by
      rw [hxj, re_mul', re_iy' het, abs_mul, abs_of_pos (Real.exp_pos t)]
    rw [e, abs_re']
    exact (GroundTheory.Automorphic.GJGlobal.norm_apply_le_norm_homeomorphMixedSpace _ _).trans
      (norm_le_pi_norm (infPartPi x) j)
  have hyb : ∀ j, |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y j)| ≤
      Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|) := by
    intro j
    rw [hyz j, re_add', re_mul', re_mul']
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, mul_add, mul_comm Bk, mul_comm Bk]
    exact add_le_add (mul_le_mul_of_nonneg_left (hBk k hk 0 j) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hBk k hk 1 j) (abs_nonneg _))
  have hT : 0 ≤ ‖infPartPi x‖ := norm_nonneg _
  have hkey : 1 / (1 + 4 * Bk) * Real.exp t *
      (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) ≤ ‖infPartPi x‖ := by
    have hS : Real.exp t * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) ≤
        4 * Bk * ‖infPartPi x‖ := by
      have h0 := mul_le_mul_of_nonneg_left (hyb 0) (Real.exp_pos t).le
      have h1 := mul_le_mul_of_nonneg_left (hyb 1) (Real.exp_pos t).le
      have h2 : Real.exp t * (Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|)) ≤
          Bk * (‖infPartPi x‖ + ‖infPartPi x‖) := by
        rw [show Real.exp t * (Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|)) =
          Bk * (Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|) by ring]
        exact mul_le_mul_of_nonneg_left (add_le_add (hxT 0) (hxT 1)) hBk0
      nlinarith
    rw [mul_assoc, one_div, inv_mul_le_iff₀ hpos]
    nlinarith
  have hm := hmaj x
  constructor
  · by_cases hmem : finPartPi x ∈ L0
    · rw [Set.indicator_of_mem hmem, mul_one] at hm
      refine hm.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      have hb : 0 ≤ 1 / (1 + 4 * Bk) * Real.exp t *
          (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) := by positivity
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) N)
    · rw [Set.indicator_of_notMem hmem, mul_zero] at hm
      exact hm.trans (by positivity)
  · intro hne
    have hmem : finPartPi x ∈ L0 := by
      by_contra hmem
      rw [Set.indicator_of_notMem hmem, mul_zero] at hm
      exact hne (norm_le_zero_iff.1 hm)
    refine ⟨(finPartPi x, k), ⟨hmem, hk⟩, ?_⟩
    have hfin : ∀ j, finPartPi x j = (z j).2 := by
      intro j
      change (x j).2 = _
      rw [hxj]
      change (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ).2 * (z j).2 = _
      rw [snd_iy' het, one_mul]
    funext j
    simp only [f, hfin]
    rw [hyz j]
    rfl
