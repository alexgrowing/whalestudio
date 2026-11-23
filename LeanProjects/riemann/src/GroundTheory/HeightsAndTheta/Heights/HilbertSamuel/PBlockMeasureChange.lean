import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMeasureChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory Matrix
  SupBoundCount

noncomputable section

namespace BlockMeasureChange

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem sup_one_le (hS : SupBoundBlock.Statement) (d : HSMBlockDatum D K ι Ω) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) →
      ∀ z ∈ mcPts (mCoordIdeal d.y),
        ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ (C * (n : ℝ) ^ ((D : ℝ) / 2)) * blockL2Norm d n F := by
  obtain ⟨C, hC⟩ := hS D K ι Ω d
  refine ⟨max C 1, le_max_right _ _, fun n hn F hF z hz => (hC n hn F hF z hz).trans ?_⟩
  have h0 : 0 ≤ blockL2Norm d n F := Real.sqrt_nonneg _
  have h1 : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) h1) h0

theorem integral_le_of_le {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {g : X → ℝ}
    {c : ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgc : ∀ x, g x ≤ c) : ∫ x, g x ∂μ ≤ c := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := c)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hg0 x)]; exact hgc x)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

theorem quad_nonneg (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (f : Fin r → MRing ι)
    (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) (a : Fin r → ℝ) :
    0 ≤ a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) := by
  rw [gram_quad d n f hf a]
  have hp : ∀ (w : ℂ) (t : ℝ), 0 ≤ ‖w‖ ^ 2 / t ^ (2 * n) := fun w t =>
    div_nonneg (sq_nonneg _) (by rw [pow_mul']; exact sq_nonneg _)
  have := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (blockPt d x)‖ ^ 2 / d.A.h (blockPt d x) ^ (2 * n)) fun x => hp _ _
  have := integral_nonneg (μ := d.dV)
    (f := fun x => ‖comb f a (conjPt (blockPt d x))‖ ^ 2 / d.A.h (conjPt (blockPt d x)) ^ (2 * n))
    fun x => hp _ _
  positivity

theorem quad_le (d d' : HSMBlockDatum D K ι Ω) (hy : d'.y = d.y) (hk : d'.k₀ = d.k₀) (hA : d'.A = d.A) (n : ℕ)
    {r : ℕ} (f : Fin r → MRing ι) (hf : ∀ k, IsMultiHomog (f k) (blockDeg d.k₀ n)) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ F : MRing ι, IsMultiHomog F (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) F)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n F) (a : Fin r → ℝ) :
    a ⬝ᵥ (blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a) ≤
      c ^ 2 * (a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a)) := by
  have hf' : ∀ k, IsMultiHomog (f k) (blockDeg d'.k₀ n) := fun k => by rw [hk]; exact hf k
  have := d'.vol.1
  have hQ := quad_nonneg d n f hf a
  set Q := a ⬝ᵥ (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ a)
  have hpt : ∀ z ∈ mcPts (mCoordIdeal d.y), ‖comb f a z‖ ^ 2 / d.A.h z ^ (2 * n) ≤ c ^ 2 * Q := by
    intro z hz
    have h1 := sup_real d n f hf hc hsup a hz
    have h0 : 0 ≤ ‖comb f a z‖ / d.A.h z ^ n :=
      div_nonneg (norm_nonneg _) (pow_pos (d.A.pos z hz.1) n).le
    have h2 := pow_le_pow_left₀ h0 h1 2
    rwa [div_pow, ← pow_mul', mul_pow, Real.sq_sqrt hQ] at h2
  have hp : ∀ (w : ℂ) (t : ℝ), 0 ≤ ‖w‖ ^ 2 / t ^ (2 * n) := fun w t =>
    div_nonneg (sq_nonneg _) (by rw [pow_mul']; exact sq_nonneg _)
  have hmem : ∀ x, blockPt d' x ∈ mcPts (mCoordIdeal d.y) := fun x => hy ▸ blockPt_mem d' x
  rw [gram_quad d' n f hf' a, hA]
  have i1 := integral_le_of_le d'.dV (fun x => hp _ _) fun x => hpt _ (hmem x)
  have i2 := integral_le_of_le d'.dV (fun x => hp _ _) fun x => hpt _ (conjPt_mem_mcPts (hmem x))
  linarith

theorem det_le {r : ℕ} {G G' : Matrix (Fin r) (Fin r) ℝ} (hG : G.IsHermitian) (hG' : G'.PosSemidef) {c : ℝ}
    (h : ∀ a, a ⬝ᵥ (G' *ᵥ a) ≤ c * (a ⬝ᵥ (G *ᵥ a))) : G'.det ≤ c ^ r * G.det := by
  have hH : (c • G - G').IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    have e1 := hG.apply i j
    have e2 := hG'.1.apply i j
    simp only [star_trivial] at e1 e2 ⊢
    simp only [Matrix.sub_apply, Matrix.smul_apply, e1, e2]
  have hpsd : (c • G - G').PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun a => ?_
    rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linarith [h a]
  have := GroundTheory.Heights₂.Heights.MCDet.re_det_mono hG' (by simpa using hpsd)
  simpa [det_smul] using this

end BlockMeasureChange

open BlockMeasureChange in

theorem BlockMeasureChange.proof (hS : SupBoundBlock.Statement) : BlockMeasureChange.Statement := by
  intro D K _ _ ι _ Ω _ _ d d' hy hk hA
  obtain ⟨C, hC, hsup⟩ := sup_one_le hS d
  obtain ⟨C', hC', hsup'⟩ := sup_one_le hS d'
  set L := max C C' with hL
  have hL1 : 1 ≤ L := hC.trans (le_max_left _ _)

  have key : ∀ n : ℕ, 1 ≤ n → |blockChi d' n - blockChi d n| ≤
      (2 * L ^ 2 * (Real.log L + D)) * ((n : ℝ) ^ D * (1 + Real.log n)) := by
    intro n hn
    have hex := exists_isSecBasisM d.y d.k₀ n
    have hb := hex.choose_spec
    choose f hf hfe using hb.1
    have hbf : hex.choose.2 = fun j => map (Int.castRingHom ℚ) (f j) := funext hfe
    have hf' : ∀ k, IsMultiHomog (f k) (blockDeg d'.k₀ n) := fun k => by rw [hk]; exact hf k
    have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
      have := hb.2.1
      simp only [hbf, aeval_map_int] at this
      exact this
    have hli' : LinearIndependent ℤ fun k => aeval d'.y (f k) := by rw [hy]; exact hli
    have hsame : ∀ (y' : (Σ k, ι k) → Ω) (k' : K), y' = d.y → k' = d.k₀ →
        ∀ h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM y' k' n p.2,
          h.choose = hex.choose := by
      rintro _ _ rfl rfl h; rfl
    have hex' : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d'.y d'.k₀ n p.2 := by
      rw [hy, hk]; exact hex
    have e1 : blockChi d n = -(1 / 2) *
        Real.log (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))).det := by
      rw [blockChi, dif_pos hex, hbf]
    have e2 : blockChi d' n = -(1 / 2) *
        Real.log (blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j))).det := by
      rw [blockChi, dif_pos hex', hsame _ _ hy hk hex', hbf]
    set G := blockGram d n (fun j => map (Int.castRingHom ℚ) (f j))
    set G' := blockGram d' n (fun j => map (Int.castRingHom ℚ) (f j))
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set s := (n : ℝ) ^ ((D : ℝ) / 2) with hs
    have hs1 : 1 ≤ s := Real.one_le_rpow hnR (by positivity)
    have hs2 : s ^ 2 = (n : ℝ) ^ D := by
      rw [hs, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1
      ring
    have hlogs : Real.log s = (D / 2) * Real.log n := by
      rw [hs, Real.log_rpow (by positivity)]
    set c := C * s
    set c' := C' * s
    have hc : 1 ≤ c := one_le_mul_of_one_le_of_one_le hC hs1
    have hc' : 1 ≤ c' := one_le_mul_of_one_le_of_one_le hC' hs1
    have hG : G.PosDef := gram_posDef d n f hf hli (by linarith) (hsup n hn)
    have hG' : G'.PosDef := gram_posDef d' n f hf' hli' (by linarith) (hsup' n hn)
    have q1 := quad_le d d' hy hk hA n f hf (by linarith) (hsup n hn)
    have q2 := quad_le d' d hy.symm hk.symm hA.symm n f hf' (by linarith) (hsup' n hn)
    have d1 := det_le hG.isHermitian hG'.posSemidef q1
    have d2 := det_le hG'.isHermitian hG.posSemidef q2
    have hr := SupBoundCount.rank_le d n f hf hli (by linarith) (hsup n hn)
    have p1 := hG.det_pos
    have p2 := hG'.det_pos
    have l1 : Real.log G'.det ≤ hex.choose.1 * Real.log (c ^ 2) + Real.log G.det := by
      rw [← Real.log_pow, ← Real.log_mul (by positivity) p1.ne']
      exact Real.log_le_log p2 d1
    have l2 : Real.log G.det ≤ hex.choose.1 * Real.log (c' ^ 2) + Real.log G'.det := by
      rw [← Real.log_pow, ← Real.log_mul (by positivity) p2.ne']
      exact Real.log_le_log p1 d2
    have lc : Real.log c ≤ Real.log L + D * Real.log n := by
      have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
      rw [Real.log_mul (by linarith) (by linarith), hlogs]
      have := Real.log_le_log (by linarith) (le_max_left C C')
      nlinarith
    have lc' : Real.log c' ≤ Real.log L + D * Real.log n := by
      have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
      rw [Real.log_mul (by linarith) (by linarith), hlogs]
      have := Real.log_le_log (by linarith) (le_max_right C C')
      nlinarith
    have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
    have hlc' : 0 ≤ Real.log c' := Real.log_nonneg hc'
    have hr0 : (0 : ℝ) ≤ (hex.choose.1 : ℝ) := Nat.cast_nonneg _
    have hrb : (hex.choose.1 : ℝ) ≤ 2 * L ^ 2 * (n : ℝ) ^ D := by
      have : c ^ 2 ≤ L ^ 2 * (n : ℝ) ^ D := by
        rw [mul_pow, hs2]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (le_max_left _ _) 2) (by positivity)
      linarith
    rw [Real.log_pow] at l1 l2
    push_cast at l1 l2
    have hdiff : |blockChi d' n - blockChi d n| ≤ hex.choose.1 * (Real.log L + D * Real.log n) := by
      have m1 := mul_le_mul_of_nonneg_left lc hr0
      have m2 := mul_le_mul_of_nonneg_left lc' hr0
      rw [e1, e2, abs_le]
      constructor <;> linarith
    have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
    have hlL : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hnD : 0 ≤ (n : ℝ) ^ D := by positivity
    refine hdiff.trans ?_
    calc (hex.choose.1 : ℝ) * (Real.log L + D * Real.log n)
        ≤ (2 * L ^ 2 * (n : ℝ) ^ D) * (Real.log L + D * Real.log n) :=
          mul_le_mul_of_nonneg_right hrb (by positivity)
      _ ≤ (2 * L ^ 2 * (Real.log L + D)) * ((n : ℝ) ^ D * (1 + Real.log n)) := by
          have : Real.log L + D * Real.log n ≤ (Real.log L + D) * (1 + Real.log n) := by
            have h3 : 0 ≤ Real.log L * Real.log n := mul_nonneg hlL hln
            have h4 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
            have e : (Real.log L + D) * (1 + Real.log n) =
                Real.log L + D * Real.log n + (D + Real.log L * Real.log n) := by ring
            rw [e]
            linarith
          calc (2 * L ^ 2 * (n : ℝ) ^ D) * (Real.log L + D * Real.log n)
              ≤ (2 * L ^ 2 * (n : ℝ) ^ D) * ((Real.log L + D) * (1 + Real.log n)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring

  have hO : (fun n : ℕ => blockChi d' n - blockChi d n) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ D * (1 + Real.log n) := by
    refine IsBigO.of_bound (2 * L ^ 2 * (Real.log L + D)) (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (key n hn).trans (le_of_eq ?_)
    congr 1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg (mul_nonneg (by positivity) (by linarith [Real.log_nonneg hnR]))]
  have hlog : (fun n : ℕ => 1 + Real.log n) =o[atTop] fun n : ℕ => (n : ℝ) := by
    have h1 := (isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto tendsto_natCast_atTop_atTop
    have h2 := Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
    exact h1.add h2
  have ho : (fun n : ℕ => (n : ℝ) ^ D * (1 + Real.log n)) =o[atTop] pw D := by
    have := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO hlog
    refine this.congr_right fun n => ?_
    simp [pw, pow_succ]
  exact hO.trans_isLittleO ho

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
