import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.MatrixEntryBounds

theorem abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  nlinarith [sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]

theorem abs_le_of_sq (t s : ℝ) (hs : 0 ≤ s) (h : t ^ 2 ≤ s ^ 2) : |t| ≤ s := by
  have := sq_le_sq.1 h
  rwa [abs_of_nonneg hs] at this

theorem core (δ C c0 x y x' y' a b c d M L R K : ℝ) (hδ : 0 < δ) (hc0 : 0 < c0) (hx : |x| ≤ C)
    (hy : c0 ≤ |y|) (hdet : |a * d - b * c| ≤ C) (hM : M * δ = 4 * C) (hL : L * c0 ^ 2 = M)
    (hR : R * c0 = C) (hK : K * (c0 ^ 2 * δ ^ 2) = 2 * C ^ 2 * δ ^ 2 + 48 * c0 ^ 2)
    (hyy : 0 < y * y') (hk : δ * ((x - x') ^ 2 + (y + y') ^ 2) ≤ 4 * (y * y'))
    (hden : y' * ((c * x + d) ^ 2 + (c * y) ^ 2) = (a * d - b * c) * y)
    (hre : x' * (c * x + d) - y' * (c * y) = a * x + b)
    (him : x' * (c * y) + y' * (c * x + d) = a * y) :
    |c| ≤ 1 + L ∧ |d| ≤ 1 + M + (1 + L) * C ∧ |a| ≤ 1 + K * M ∧ |b| ≤ (1 + K * M) * (1 + R) * |y| := by
  have hC : 0 ≤ C := (abs_nonneg x).trans hx
  have hy0 : 0 < |y| := hc0.trans_le hy
  have hy'0 : y' ≠ 0 := right_ne_zero_of_mul hyy.ne'
  have hay' : 0 < |y'| := abs_pos.2 hy'0
  have hyy' : y * y' = |y| * |y'| := by rw [← abs_mul, abs_of_pos hyy]
  have h1 : δ * y ^ 2 ≤ 4 * (y * y') := by
    linarith [mul_nonneg hδ.le (sq_nonneg (x - x')), mul_nonneg hδ.le (sq_nonneg y'), mul_pos hδ hyy]
  have h2 : δ * y' ^ 2 ≤ 4 * (y * y') := by
    linarith [mul_nonneg hδ.le (sq_nonneg (x - x')), mul_nonneg hδ.le (sq_nonneg y), mul_pos hδ hyy]
  have h3 : δ * (x - x') ^ 2 ≤ 4 * (y * y') := by
    linarith [mul_nonneg hδ.le (sq_nonneg y'), mul_nonneg hδ.le (sq_nonneg y), mul_pos hδ hyy]
  set N := (c * x + d) ^ 2 + (c * y) ^ 2 with hN
  have e : (y * y') * (δ * N) = (a * d - b * c) * (δ * y ^ 2) := by linear_combination (δ * y) * hden
  have e2 : (a * d - b * c) * (δ * y ^ 2) ≤ C * (4 * (y * y')) := by
    calc (a * d - b * c) * (δ * y ^ 2) ≤ |a * d - b * c| * (δ * y ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ C * (δ * y ^ 2) := mul_le_mul_of_nonneg_right hdet (by positivity)
      _ ≤ C * (4 * (y * y')) := mul_le_mul_of_nonneg_left h1 hC
  have hδN : δ * N ≤ 4 * C := le_of_mul_le_mul_left (by linarith [e, e2]) hyy
  have hNM : N ≤ M := le_of_mul_le_mul_right (by linarith [hδN, hM]) hδ
  have hN0 : 0 ≤ N := by positivity
  have hcy : (c * y) ^ 2 ≤ M := by linarith [sq_nonneg (c * x + d)]
  have hcxd : (c * x + d) ^ 2 ≤ M := by linarith [sq_nonneg (c * y)]
  have hc0y : c0 ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ hc0.le hy 2
  have hc2 : c ^ 2 ≤ L := by
    have : c ^ 2 * c0 ^ 2 ≤ L * c0 ^ 2 := by
      rw [hL]; linarith [mul_le_mul_of_nonneg_left hc0y (sq_nonneg c)]
    exact le_of_mul_le_mul_right this (by positivity)
  have hc : |c| ≤ 1 + L := (abs_le_one_add_sq c).trans (by linarith)
  have hcxd' : |c * x + d| ≤ 1 + M := (abs_le_one_add_sq _).trans (by linarith)
  have hcx : |c * x| ≤ (1 + L) * C := by
    rw [abs_mul]; exact mul_le_mul hc hx (abs_nonneg _) ((abs_nonneg c).trans hc)
  have hd : |d| ≤ 1 + M + (1 + L) * C := by
    have a1 := abs_le.1 hcxd'
    have a2 := abs_le.1 hcx
    exact abs_le.2 ⟨by linarith [a1.1, a2.2], by linarith [a1.2, a2.1]⟩

  have hy' : δ * |y'| ≤ 4 * |y| := by
    have : |y'| * (δ * |y'|) ≤ |y'| * (4 * |y|) := by
      calc |y'| * (δ * |y'|) = δ * y' ^ 2 := by rw [← sq_abs y']; ring
        _ ≤ 4 * (y * y') := h2
        _ = |y'| * (4 * |y|) := by rw [hyy']; ring
    exact le_of_mul_le_mul_left this hay'
  have A2 : δ ^ 2 * y' ^ 2 ≤ 16 * y ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hy' 2
    rw [mul_pow, mul_pow, sq_abs, sq_abs] at this
    linarith
  have A1 : δ ^ 2 * (x - x') ^ 2 ≤ 16 * y ^ 2 := by
    have h4 : δ * (δ * (x - x') ^ 2) ≤ δ * (4 * (y * y')) := mul_le_mul_of_nonneg_left h3 hδ.le
    have h5 : δ * (4 * (y * y')) ≤ 16 * y ^ 2 := by
      rw [hyy']
      linarith [mul_le_mul_of_nonneg_left hy' (abs_nonneg y), sq_abs y]
    linarith
  have A3 : c0 ^ 2 * x ^ 2 ≤ C ^ 2 * y ^ 2 := by
    have hx2 : x ^ 2 ≤ C ^ 2 := by rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
    have := mul_le_mul hc0y hx2 (sq_nonneg _) (sq_nonneg _)
    linarith
  have hW : x' ^ 2 + y' ^ 2 ≤ K * y ^ 2 := by
    have hp : 0 < c0 ^ 2 * δ ^ 2 := by positivity
    refine le_of_mul_le_mul_right ?_ hp
    have : K * y ^ 2 * (c0 ^ 2 * δ ^ 2) = (2 * C ^ 2 * δ ^ 2 + 48 * c0 ^ 2) * y ^ 2 := by rw [← hK]; ring
    rw [this]
    linarith [mul_le_mul_of_nonneg_left A1 (sq_nonneg c0), mul_le_mul_of_nonneg_left A2 (sq_nonneg c0),
      mul_le_mul_of_nonneg_left A3 (sq_nonneg δ), mul_nonneg (sq_nonneg (c0 * δ)) (sq_nonneg (2 * x - x'))]
  have E : (a * x + b) ^ 2 + (a * y) ^ 2 = (x' ^ 2 + y' ^ 2) * N := by rw [hN, ← hre, ← him]; ring
  have hKM : (x' ^ 2 + y' ^ 2) * N ≤ K * y ^ 2 * M :=
    mul_le_mul hW hNM hN0 ((add_nonneg (sq_nonneg _) (sq_nonneg _)).trans hW)
  have hy2 : 0 < y ^ 2 := by rw [← sq_abs]; positivity
  have hKM0 : 0 ≤ K * M := by
    have : 0 ≤ K * M * y ^ 2 := by linarith [sq_nonneg (a * x + b), sq_nonneg (a * y)]
    exact nonneg_of_mul_nonneg_left this hy2
  have ha2 : a ^ 2 ≤ K * M := by
    have : a ^ 2 * y ^ 2 ≤ K * M * y ^ 2 := by linarith [sq_nonneg (a * x + b)]
    exact le_of_mul_le_mul_right this hy2
  have ha : |a| ≤ 1 + K * M := (abs_le_one_add_sq a).trans (by linarith)
  have hb1 : |a * x + b| ≤ (1 + K * M) * |y| := by
    apply abs_le_of_sq _ _ (by positivity)
    rw [mul_pow, sq_abs]
    linarith [sq_nonneg (a * y), mul_le_mul_of_nonneg_right (show K * M ≤ (1 + K * M) ^ 2 by linarith [sq_nonneg (K * M)])
      (sq_nonneg y)]
  have hR0 : 0 ≤ R := by
    by_contra h
    have := mul_neg_of_neg_of_pos (not_le.1 h) hc0
    linarith
  have hxR : |x| ≤ R * |y| := hx.trans (by rw [← hR]; exact mul_le_mul_of_nonneg_left hy hR0)
  have hax : |a * x| ≤ (1 + K * M) * (R * |y|) := by
    rw [abs_mul]; exact mul_le_mul ha hxR (abs_nonneg _) (by linarith)
  refine ⟨hc, hd, ha, ?_⟩
  have b1 := abs_le.1 hb1
  have b2 := abs_le.1 hax
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [b1.1, b1.2, b2.1, b2.2]

end UpperTheory.Esk.MatrixEntryBounds

namespace UpperTheory.Esk.MatrixEntryBounds

theorem main : ∀ δ C c : ℝ, 0 < δ → 0 < c → ∃ B : ℝ, ∀ (g : GL (Fin 2) ℝ) (z : P), |z.1.re| ≤ C → c ≤ |z.1.im| →
    |g.val.det| ≤ C → δ ≤ kap z (g • z) → |g 1 0| ≤ B ∧ |g 0 0| ≤ B ∧ |g 1 1| ≤ B ∧ |g 0 1| ≤ B * |z.1.im| := by
  intro δ C c0 hδ hc0
  have hM : (4 * C / δ) * δ = 4 * C := div_mul_cancel₀ _ hδ.ne'
  have hL : (4 * C / δ / c0 ^ 2) * c0 ^ 2 = 4 * C / δ := div_mul_cancel₀ _ (by positivity)
  have hR : (C / c0) * c0 = C := div_mul_cancel₀ _ hc0.ne'
  have hK : (2 * C ^ 2 / c0 ^ 2 + 48 / δ ^ 2) * (c0 ^ 2 * δ ^ 2) = 2 * C ^ 2 * δ ^ 2 + 48 * c0 ^ 2 := by
    field_simp
  refine ⟨max (max (1 + 4 * C / δ / c0 ^ 2) (1 + 4 * C / δ + (1 + 4 * C / δ / c0 ^ 2) * C))
    (max (1 + (2 * C ^ 2 / c0 ^ 2 + 48 / δ ^ 2) * (4 * C / δ))
      ((1 + (2 * C ^ 2 / c0 ^ 2 + 48 / δ ^ 2) * (4 * C / δ)) * (1 + C / c0))), ?_⟩
  intro g z hx hy hdet hk
  unfold kap at hk
  split_ifs at hk with hyy
  swap
  · exact absurd hk (not_le.2 hδ)
  have hn : ‖z.1 - (starRingEnd ℂ) (g • z).1‖ ^ 2 = (z.1.re - (g • z).1.re) ^ 2 + (z.1.im + (g • z).1.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hpos : 0 < (z.1.re - (g • z).1.re) ^ 2 + (z.1.im + (g • z).1.im) ^ 2 := by
    nlinarith [sq_nonneg (z.1.re - (g • z).1.re), sq_nonneg (z.1.im - (g • z).1.im)]
  rw [hn, le_div_iff₀ hpos] at hk
  have hns : Complex.normSq (den g z.1) = (g 1 0 * z.1.re + g 1 1) ^ 2 + (g 1 0 * z.1.im) ^ 2 := by
    rw [Complex.normSq_apply]; simp [den]; ring
  have hne : Complex.normSq (den g z.1) ≠ 0 := (Complex.normSq_pos.2 (den_ne g z.2)).ne'
  have hden : (g • z).1.im * ((g 1 0 * z.1.re + g 1 1) ^ 2 + (g 1 0 * z.1.im) ^ 2) =
      (g 0 0 * g 1 1 - g 0 1 * g 1 0) * z.1.im := by
    rw [← hns, coe_smul, im_div, det_eq, div_mul_cancel₀ _ hne]
  have hW : (g • z).1 * den g z.1 = num g z.1 := by rw [coe_smul, div_mul_cancel₀ _ (den_ne g z.2)]
  have hre := congrArg Complex.re hW
  have him := congrArg Complex.im hW
  simp [num, den, Complex.mul_re, Complex.mul_im] at hre him
  obtain ⟨h1, h2, h3, h4⟩ := core δ C c0 z.1.re z.1.im (g • z).1.re (g • z).1.im (g 0 0) (g 0 1) (g 1 0) (g 1 1)
    _ _ _ _ hδ hc0 hx hy (by rwa [det_eq] at hdet) hM hL hR hK hyy hk hden
    (by linear_combination hre) (by linear_combination him)
  refine ⟨h1.trans ((le_max_left _ _).trans (le_max_left _ _)), h3.trans ((le_max_left _ _).trans (le_max_right _ _)),
    h2.trans ((le_max_right _ _).trans (le_max_left _ _)),
    h4.trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (abs_nonneg _))⟩

end UpperTheory.Esk.MatrixEntryBounds

theorem UpperTheory.Esk.dEntry : UpperTheory.Esk.DEntry := UpperTheory.Esk.MatrixEntryBounds.main
