import Mathlib

open MeasureTheory Metric Set Finset Filter Topology

namespace GlobalTheory.ProdNormSum

lemma finrank_complexSpace (n : ℕ) : Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]

lemma integral_Ioi_inv_one_add_pow_five :
    IntegrableOn (fun y : ℝ => ((1 + y) ^ 5)⁻¹) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), ((1 + y) ^ 5)⁻¹ = 1 / 4 := by
  set g : ℝ → ℝ := fun y => -(((1 + y) ^ 4)⁻¹ / 4) with hg
  have hder' : ∀ x : ℝ, 0 ≤ x → HasDerivAt g (((1 + x) ^ 5)⁻¹) x := by
    intro x hx
    have hx0 : (0 : ℝ) < 1 + x := by linarith
    have h1 : HasDerivAt (fun y : ℝ => (1 + y) ^ 4) (4 * (1 + x) ^ 3) x := by
      have := (hasDerivAt_pow 4 (1 + x)).comp x ((hasDerivAt_id x).const_add 1)
      simp only [Nat.cast_ofNat, mul_one] at this
      exact this
    have h2 := (h1.inv (by positivity)).div_const 4 |>.neg
    have h3 : HasDerivAt g (-(-(4 * (1 + x) ^ 3) / ((1 + x) ^ 4) ^ 2 / 4)) x := h2
    refine h3.congr_deriv ?_
    have : (1 + x) ^ 4 ≠ 0 := by positivity
    have : (1 + x) ^ 5 ≠ 0 := by positivity
    field_simp
  have hder : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (((1 + x) ^ 5)⁻¹) x :=
    fun x hx => hder' x (le_of_lt hx)
  have hcont : ContinuousWithinAt g (Ici 0) 0 :=
    (hder' 0 le_rfl).continuousAt.continuousWithinAt
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ ((1 + x) ^ 5)⁻¹ := by
    intro x hx
    have : (0:ℝ) < x := hx
    positivity
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (1 + y) ^ 4) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
    have h2 := (tendsto_inv_atTop_zero.comp h1).div_const 4 |>.neg
    simpa [g, Function.comp_def] using h2
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hder hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hder hpos hlim]
  simp [g]

end GlobalTheory.ProdNormSum

namespace GlobalTheory.ProdNormSum

lemma integral_inv_one_add_norm_pow_le (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun x : EuclideanSpace ℂ (Fin n) => ((1 + ‖x‖) ^ (2 * n + 4))⁻¹) ∧
      ∫ x : EuclideanSpace ℂ (Fin n), ((1 + ‖x‖) ^ (2 * n + 4))⁻¹ ≤
        ((n : ℝ) / 2 * 4 ^ n) * (volume : Measure (EuclideanSpace ℂ (Fin n))).real (ball 0 (1 / 2)) := by
  have hfr := finrank_complexSpace n
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfr]; omega)
  refine ⟨?_, ?_⟩
  · have h := integrable_one_add_norm (E := EuclideanSpace ℂ (Fin n))
      (μ := volume) (r := ((2 * n + 4 : ℕ) : ℝ)) (by rw [hfr]; push_cast; linarith)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  · have hp := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℂ (Fin n)))
      (fun y : ℝ => ((1 + y) ^ (2 * n + 4))⁻¹)
    rw [hfr] at hp
    simp only [nsmul_eq_mul, smul_eq_mul] at hp
    rw [hp]
    obtain ⟨hI, hI4⟩ := integral_Ioi_inv_one_add_pow_five
    have hle : ∫ y in Ioi (0 : ℝ), y ^ (2 * n - 1) * ((1 + y) ^ (2 * n + 4))⁻¹ ≤ 1 / 4 := by
      rw [← hI4]
      refine integral_mono_of_nonneg ?_ hI ?_
      · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => ?_)
        have : (0 : ℝ) < y := hy
        simp only [Pi.zero_apply]
        positivity
      · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => ?_)
        have hy0 : (0 : ℝ) < y := hy
        have hpow : (1 + y) ^ (2 * n + 4) = (1 + y) ^ (2 * n - 1) * (1 + y) ^ 5 := by
          rw [← pow_add]; congr 1; omega
        show y ^ (2 * n - 1) * ((1 + y) ^ (2 * n + 4))⁻¹ ≤ ((1 + y) ^ 5)⁻¹
        rw [hpow, mul_inv, ← mul_assoc]
        have h1 : y ^ (2 * n - 1) * ((1 + y) ^ (2 * n - 1))⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, ← div_pow]
          exact pow_le_one₀ (by positivity) ((div_le_one (by linarith)).2 (by linarith))
        exact mul_le_of_le_one_left (by positivity) h1
    have hball : (volume : Measure (EuclideanSpace ℂ (Fin n))).real (ball 0 1) =
        4 ^ n * (volume : Measure (EuclideanSpace ℂ (Fin n))).real (ball 0 (1 / 2)) := by
      simp only [Measure.real]
      rw [Measure.addHaar_ball_of_pos _ _ (by norm_num : (0 : ℝ) < 1 / 2), hfr,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ← mul_assoc, pow_mul, ← mul_pow]
      norm_num
    rw [hball]
    have hc : 0 ≤ (volume : Measure (EuclideanSpace ℂ (Fin n))).real (ball 0 (1 / 2)) :=
      measureReal_nonneg
    have h4 : (0 : ℝ) ≤ 4 ^ n := by positivity
    have h2n : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by positivity
    have key := mul_le_mul_of_nonneg_left hle (show 0 ≤ ((2 * n : ℕ) : ℝ) *
      (4 ^ n * (volume : Measure (EuclideanSpace ℂ (Fin n))).real (ball 0 (1 / 2))) by positivity)
    calc _ = ((2 * n : ℕ) : ℝ) * (4 ^ n * (volume : Measure (EuclideanSpace ℂ (Fin n))).real (ball 0 (1 / 2))) *
          ∫ y in Ioi (0 : ℝ), y ^ (2 * n - 1) * ((1 + y) ^ (2 * n + 4))⁻¹ := by ring
      _ ≤ _ := key
      _ = _ := by push_cast; ring

end GlobalTheory.ProdNormSum

namespace GlobalTheory.ProdNormSum

lemma const_le_exp (n : ℕ) :
    (3 : ℝ) ^ (2 * n + 5) * ((3 / 2) ^ (2 * n + 4) * ((n : ℝ) / 2 * 4 ^ n)) ≤
      Real.exp (6 * n + 9) := by
  have e : (3 : ℝ) ^ (2 * n + 5) * ((3 / 2) ^ (2 * n + 4) * ((n : ℝ) / 2 * 4 ^ n)) =
      (81 : ℝ) ^ n * n * (19683 / 32) := by
    rw [pow_add, pow_add, pow_mul, pow_mul,
      show ((3 : ℝ) ^ 2) = 9 by norm_num, show ((3 / 2 : ℝ) ^ 2) = 9 / 4 by norm_num,
      show (81 : ℝ) = 9 * (9 / 4) * 4 by norm_num, mul_pow, mul_pow]
    ring
  rw [e]
  have hn : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have h1 : (81 : ℝ) ^ n * n * (19683 / 32) ≤ (162 : ℝ) ^ n * (19683 / 32) := by
    rw [show (162 : ℝ) = 81 * 2 by norm_num, mul_pow]
    gcongr
  have h2 : (162 : ℝ) ^ n * (19683 / 32) ≤ ((2.7 : ℝ) ^ 6) ^ n * (2.7 : ℝ) ^ 9 := by
    gcongr
    · norm_num
    · norm_num
  have h3 : ((2.7 : ℝ) ^ 6) ^ n * (2.7 : ℝ) ^ 9 ≤ Real.exp (6 * n + 9) := by
    rw [← pow_mul, ← pow_add]
    have hx : Real.exp (6 * n + 9) = Real.exp 1 ^ (6 * n + 9) := by
      rw [Real.exp_one_pow]; push_cast; ring_nf
    rw [hx, mul_comm 6 n]
    have := Real.exp_one_gt_d9
    exact pow_le_pow_left₀ (by norm_num) (by linarith) _
  linarith

lemma sum_prod_inv_one_add_norm_pow_le (ι : Type) [Fintype ι] (n : ℕ) (hn : 1 ≤ n)
    (s : Finset (ι → EuclideanSpace ℂ (Fin n)))
    (hsep : ∀ w ∈ s, ∀ w' ∈ s, w ≠ w' → ∃ τ, 1 ≤ ‖w τ - w' τ‖) :
    ∑ w ∈ s, ∏ τ, ((1 + ‖w τ‖) ^ (2 * n + 4))⁻¹ ≤
      ((3 / 2) ^ (2 * n + 4) * ((n : ℝ) / 2 * 4 ^ n)) ^ Fintype.card ι := by
  classical
  set h : EuclideanSpace ℂ (Fin n) → ℝ := fun x => ((1 + ‖x‖) ^ (2 * n + 4))⁻¹ with hh
  set G : (ι → EuclideanSpace ℂ (Fin n)) → ℝ := fun u => ∏ τ, h (u τ) with hG
  set B : (ι → EuclideanSpace ℂ (Fin n)) → Set (ι → EuclideanSpace ℂ (Fin n)) :=
    fun w => Set.univ.pi (fun τ => ball (w τ) (1 / 2)) with hB
  set vb : ℝ := (volume : Measure (EuclideanSpace ℂ (Fin n))).real (ball 0 (1 / 2)) with hvb
  set c : ℝ := (3 / 2) ^ (2 * n + 4) with hc
  set d : ℕ := Fintype.card ι with hd
  obtain ⟨hint, hintle⟩ := integral_inv_one_add_norm_pow_le n hn
  have hvb0 : 0 < vb := ENNReal.toReal_pos (measure_ball_pos _ _ (by norm_num)).ne'
    measure_ball_lt_top.ne
  have hh0 : ∀ x, 0 ≤ h x := fun x => by simp only [hh]; positivity
  have hG0 : ∀ u, 0 ≤ G u := fun u => Finset.prod_nonneg fun τ _ => hh0 _
  have hBmeas : ∀ w, MeasurableSet (B w) := fun w => MeasurableSet.univ_pi fun _ => measurableSet_ball
  have hBvol : ∀ w, volume (B w) = ∏ τ : ι, volume (ball (0 : EuclideanSpace ℂ (Fin n)) (1 / 2)) := by
    intro w
    simp only [hB, volume_pi_pi]
    exact Finset.prod_congr rfl fun τ _ => Measure.addHaar_ball_center _ _ _
  have hBfin : ∀ w, volume (B w) ≠ ⊤ := fun w => by
    rw [hBvol]; exact ENNReal.prod_ne_top fun _ _ => measure_ball_lt_top.ne
  have hBreal : ∀ w, (volume : Measure (ι → EuclideanSpace ℂ (Fin n))).real (B w) = vb ^ d := by
    intro w
    simp only [Measure.real, hBvol, ENNReal.toReal_prod, Finset.prod_const, Finset.card_univ, hvb, hd,
      ENNReal.toReal_pow]
  have hGint : Integrable G := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ => h) (fun _ => hint)
  have hGeq : ∫ u, G u = (∫ x, h x) ^ d := integral_fintype_prod_volume_eq_pow h

  have hpt : ∀ w, ∀ u ∈ B w, ∏ τ, h (w τ) ≤ c ^ d * G u := by
    intro w u hu
    have hu' : ∀ τ, u τ ∈ ball (w τ) (1 / 2) := fun τ => hu τ (Set.mem_univ τ)
    have : ∀ τ, h (w τ) ≤ c * h (u τ) := by
      intro τ
      have hd' : ‖u τ‖ ≤ ‖w τ‖ + 1 / 2 := by
        have := mem_ball.1 (hu' τ)
        rw [dist_eq_norm] at this
        have := norm_le_insert' (u τ) (w τ)
        linarith [norm_sub_rev (u τ) (w τ)]
      have h1 : 1 + ‖u τ‖ ≤ 3 / 2 * (1 + ‖w τ‖) := by linarith [norm_nonneg (w τ)]
      simp only [hh, hc]
      rw [← inv_inv ((3 / 2 : ℝ) ^ (2 * n + 4)), ← mul_inv, inv_le_inv₀ (by positivity) (by positivity),
        ← inv_pow, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [inv_mul_le_iff₀ (by norm_num)]
      linarith
    calc ∏ τ, h (w τ) ≤ ∏ τ, (c * h (u τ)) :=
          Finset.prod_le_prod (fun τ _ => hh0 _) fun τ _ => this τ
      _ = c ^ d * G u := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hbox : ∀ w, (∏ τ, h (w τ)) * vb ^ d ≤ ∫ u in B w, c ^ d * G u := by
    intro w
    have e : (∏ τ, h (w τ)) * vb ^ d = ∫ u in B w, (∏ τ, h (w τ)) := by
      rw [setIntegral_const, hBreal, smul_eq_mul, mul_comm]
    rw [e]
    exact setIntegral_mono_on (integrableOn_const (hBfin w)) ((hGint.const_mul _).integrableOn)
      (hBmeas w) (hpt w)
  have hdisj : (s : Set (ι → EuclideanSpace ℂ (Fin n))).Pairwise (Function.onFun Disjoint B) := by
    intro w hw w' hw' hne
    obtain ⟨τ, hτ⟩ := hsep w hw w' hw' hne
    refine Set.disjoint_left.2 fun u hu hu' => ?_
    have a := mem_ball.1 (hu τ (Set.mem_univ τ))
    have b := mem_ball.1 (hu' τ (Set.mem_univ τ))
    have := dist_triangle_left (w τ) (w' τ) (u τ)
    rw [dist_eq_norm] at this
    linarith
  have hsum : (∑ w ∈ s, ∏ τ, h (w τ)) * vb ^ d ≤ c ^ d * (∫ x, h x) ^ d := by
    rw [Finset.sum_mul]
    calc ∑ w ∈ s, (∏ τ, h (w τ)) * vb ^ d ≤ ∑ w ∈ s, ∫ u in B w, c ^ d * G u :=
          Finset.sum_le_sum fun w _ => hbox w
      _ = ∫ u in ⋃ w ∈ s, B w, c ^ d * G u :=
          (integral_biUnion_finset s (fun w _ => hBmeas w) hdisj
            (fun w _ => (hGint.const_mul _).integrableOn)).symm
      _ ≤ ∫ u, c ^ d * G u :=
          setIntegral_le_integral (hGint.const_mul _)
            (Eventually.of_forall fun u => mul_nonneg (by positivity) (hG0 u))
      _ = c ^ d * (∫ x, h x) ^ d := by rw [integral_const_mul, hGeq]
  have hI0 : 0 ≤ ∫ x, h x := integral_nonneg hh0
  have hfin : c ^ d * (∫ x, h x) ^ d ≤ (c * ((n : ℝ) / 2 * 4 ^ n)) ^ d * vb ^ d := by
    rw [← mul_pow, ← mul_pow, mul_assoc]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hintle (by positivity)) _
  have hpos : 0 < vb ^ d := pow_pos hvb0 _
  exact le_of_mul_le_mul_right (hsum.trans hfin) hpos

end GlobalTheory.ProdNormSum

namespace GlobalTheory.ProdNormSum

theorem lattice_sum_le : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ)
    (Λ : AddSubgroup (ι → EuclideanSpace ℂ (Fin n))) (R : ℝ), 1 ≤ n → 1 < R →
    (∀ w ∈ Λ, w ≠ 0 → R ≤ ∏ τ, ‖w τ‖) → ∀ s : Finset (ι → EuclideanSpace ℂ (Fin n)),
    (∀ w ∈ s, w ∈ Λ ∧ w ≠ 0) →
    ∑ w ∈ s, ∏ τ, (((1 + ‖w τ‖) / 3) ^ (2 * n + 5))⁻¹ ≤
      Real.exp ((6 * n + 9) * Fintype.card ι) / R := by
  intro ι _ _ n Λ R hn hR hΛ s hs
  classical
  have hR0 : 0 < R := by linarith

  have hsep : ∀ w ∈ s, ∀ w' ∈ s, w ≠ w' → ∃ τ, 1 ≤ ‖w τ - w' τ‖ := by
    intro w hw w' hw' hne
    by_contra hcon
    push_neg at hcon
    have hmem : w - w' ∈ Λ := Λ.sub_mem (hs w hw).1 (hs w' hw').1
    have hne0 : w - w' ≠ 0 := sub_ne_zero.2 hne
    have h1 := hΛ _ hmem hne0
    have h2 : ∏ τ, ‖(w - w') τ‖ ≤ 1 :=
      Finset.prod_le_one (fun τ _ => norm_nonneg _) fun τ _ => (hcon τ).le
    linarith
  have hP := sum_prod_inv_one_add_norm_pow_le ι n hn s hsep
  set d := Fintype.card ι with hd
  set K : ℝ := (3 : ℝ) ^ (2 * n + 5) with hK

  have hterm : ∀ w ∈ s, ∏ τ, (((1 + ‖w τ‖) / 3) ^ (2 * n + 5))⁻¹ ≤
      K ^ d * (∏ τ, ((1 + ‖w τ‖) ^ (2 * n + 4))⁻¹) * R⁻¹ := by
    intro w hw
    have hx : ∀ τ, 0 < 1 + ‖w τ‖ := fun τ => by positivity
    have e : ∀ τ, (((1 + ‖w τ‖) / 3) ^ (2 * n + 5))⁻¹ =
        K * ((1 + ‖w τ‖) ^ (2 * n + 4))⁻¹ * (1 + ‖w τ‖)⁻¹ := by
      intro τ
      have := (hx τ).ne'
      rw [hK, div_pow, pow_succ]
      field_simp
    simp only [e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hd]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.prod_inv_distrib]
    have h1 := hΛ w (hs w hw).1 (hs w hw).2
    have h2 : ∏ τ, ‖w τ‖ ≤ ∏ τ, (1 + ‖w τ‖) :=
      Finset.prod_le_prod (fun τ _ => norm_nonneg _) fun τ _ => by linarith
    exact inv_anti₀ hR0 (h1.trans h2)
  calc ∑ w ∈ s, ∏ τ, (((1 + ‖w τ‖) / 3) ^ (2 * n + 5))⁻¹
      ≤ ∑ w ∈ s, K ^ d * (∏ τ, ((1 + ‖w τ‖) ^ (2 * n + 4))⁻¹) * R⁻¹ := Finset.sum_le_sum hterm
    _ = K ^ d * (∑ w ∈ s, ∏ τ, ((1 + ‖w τ‖) ^ (2 * n + 4))⁻¹) * R⁻¹ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ K ^ d * ((3 / 2) ^ (2 * n + 4) * ((n : ℝ) / 2 * 4 ^ n)) ^ d * R⁻¹ := by
      gcongr
    _ = (K * ((3 / 2) ^ (2 * n + 4) * ((n : ℝ) / 2 * 4 ^ n))) ^ d * R⁻¹ := by
      rw [mul_pow K]
    _ ≤ Real.exp (6 * n + 9) ^ d * R⁻¹ := by
      gcongr
      exact const_le_exp n
    _ = Real.exp ((6 * n + 9) * Fintype.card ι) / R := by
      rw [div_eq_mul_inv, mul_comm (6 * (n : ℝ) + 9), Real.exp_nat_mul]

end GlobalTheory.ProdNormSum
