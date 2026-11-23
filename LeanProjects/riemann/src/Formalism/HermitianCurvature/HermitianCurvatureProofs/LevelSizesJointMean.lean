import Formalism.HermitianCurvature.StatementJ

namespace Formalism.FourierDecayAlt.P.Jx2

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

open scoped nonZeroDivisors ComplexConjugate

theorem t_MajIsProf : MajIsProf := by
  intro E W _ _ D e hP ρ l
  simp only [TB.Data.maj, prof]
  refine Fintype.prod_equiv e _ _ (fun v => ?_)
  simp only [hP v l, Equiv.symm_apply_apply]

theorem t_BoxSumLattice : BoxSumLattice := by
  intro hBS
  obtain ⟨C₀, hC₀⟩ := hBS
  refine ⟨max |C₀| 1, le_max_right _ _, ?_⟩
  intro E _ _ _ aa L x K Θ a haa hL hx hK ha hΘ hprod
  have hΘpos : 0 < Θ := by linarith
  have hapos : 0 < a := by linarith
  have hC1 : 0 < max |C₀| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hwl : ∀ (w : InfinitePlace E) (l : E), 0 ≤ w l := by
    intro w l
    first
    | exact w.nonneg l
    | exact apply_nonneg w l
    | exact w.1.nonneg l
  have hfac : ∀ (z : InfinitePlace E → ℝ) (l : E) (w : InfinitePlace E), 0 ≤ z w →
      0 ≤ min 1 ((z w / w l) ^ K) := fun z l w hz =>
    le_min zero_le_one (pow_nonneg (div_nonneg hz (hwl w l)) K)
  have hnonneg : ∀ l, 0 ≤ prof x K l := by
    intro l
    simp only [prof]
    exact Finset.prod_nonneg (fun w _ => hfac x l w (hx w))
  have hZpos : 0 < a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
    have h1 : 0 < a ^ ((K : ℝ) - 5 / 2) := Real.rpow_pos_of_pos hapos _
    have h2 : 0 < Θ ^ (-((K : ℝ) - 5 / 2)) := Real.rpow_pos_of_pos hΘpos _
    exact mul_pos h1 h2
  have hep : 0 ≤ (max |C₀| 1 * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^
      Fintype.card (InfinitePlace E) := by
    rw [mul_assoc]
    exact pow_nonneg (mul_pos hC1 hZpos).le _
  unfold TA.LatSum
  refine ⟨hnonneg, ?_⟩
  intro S hS
  by_cases hz : ∃ w, x w = 0
  · obtain ⟨w₀, hw₀⟩ := hz
    have h0 : ∀ l, prof x K l = 0 := by
      intro l
      simp only [prof]
      apply Finset.prod_eq_zero (Finset.mem_univ w₀)
      rw [hw₀, zero_div, zero_pow (by omega)]
      exact min_eq_right zero_le_one
    simp only [h0, Finset.sum_const_zero]
    exact hep
  push_neg at hz
  have hxpos : ∀ w, 0 < x w := fun w => lt_of_le_of_ne (hx w) (hz w).symm
  have hn0 : Fintype.card (InfinitePlace E) ≠ 0 := Fintype.card_ne_zero
  have hPpos : 0 < ∏ w, x w := Finset.prod_pos (fun w _ => hxpos w)
  have haΘ : 0 < (a / Θ) ^ Fintype.card (InfinitePlace E) := pow_pos (div_pos hapos hΘpos) _
  have hNpos : 0 < √(FractionalIdeal.absNorm aa : ℝ) := by
    by_contra hcon
    push_neg at hcon
    nlinarith [haΘ, hPpos, hprod, hcon]
  set n := Fintype.card (InfinitePlace E) with hn
  set P := ∏ w, x w with hP
  set N := √(FractionalIdeal.absNorm aa : ℝ) with hN
  set T := (a / Θ) ^ n * N with hT
  have hTpos : 0 < T := mul_pos haΘ hNpos
  set lam := (T / P) ^ ((n : ℝ)⁻¹) with hlam
  have hlam1 : 1 ≤ lam := Real.one_le_rpow ((one_le_div hPpos).mpr hprod) (by positivity)
  have hlamn : lam ^ n = T / P := Real.rpow_inv_natCast_pow (div_pos hTpos hPpos).le hn0
  set y : InfinitePlace E → ℝ := fun w => lam * x w with hy
  have hypos : ∀ w, 0 < y w := fun w => mul_pos (by linarith) (hxpos w)
  have hxy : ∀ w, x w ≤ y w := fun w => le_mul_of_one_le_left (hx w) hlam1
  have hprody : ∏ w, y w = T := by
    simp only [hy, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    rw [← hn, hlamn, ← hP, div_mul_cancel₀ _ hPpos.ne']
  have heq : (Θ / a) ^ n = N / ∏ w, y w := by
    rw [hprody, hT, mul_comm, ← div_div, div_self hNpos.ne', one_div, ← inv_pow, inv_div]
  have hS' : ∀ l ∈ S, l ∈ aa ∧ l ≠ 0 := fun l hl => ⟨hL l (hS l hl).1, (hS l hl).2⟩
  have h2 : 2 < Θ / a := by
    first
    | (rw [lt_div_iff₀ hapos]; linarith)
    | (rw [lt_div_iff hapos]; linarith)
  have h3 : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hB := hC₀ E aa haa y (Θ / a) K hypos h2 h3 heq S hS'
  have hZ : (Θ / a) ^ (-((K : ℝ) - 5 / 2)) = a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
    rw [Real.div_rpow hΘpos.le hapos.le, Real.rpow_neg hapos.le, div_inv_eq_mul, mul_comm]
  calc ∑ l ∈ S, prof x K l
      ≤ ∑ l ∈ S, ∏ w, min 1 ((y w / w l) ^ (K : ℝ)) := by
        apply Finset.sum_le_sum
        intro l _
        simp only [prof]
        apply Finset.prod_le_prod (fun w _ => hfac x l w (hx w))
        intro w _
        rw [Real.rpow_natCast]
        apply min_le_min_left
        have hd : x w / w l ≤ y w / w l := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (hxy w) (inv_nonneg.mpr (hwl w l))
        have hd0 : 0 ≤ x w / w l := div_nonneg (hx w) (hwl w l)
        first
        | exact pow_le_pow_left hd0 hd K
        | exact pow_le_pow_left₀ hd0 hd K
    _ ≤ (C₀ * (Θ / a) ^ (-((K : ℝ) - 5 / 2))) ^ n := hB
    _ ≤ (max |C₀| 1 * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^ n := by
        rw [hZ, mul_assoc (max |C₀| 1)]
        have hle : |C₀| * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ≤
            max |C₀| 1 * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hZpos.le
        have h0 : 0 ≤ |C₀| * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) :=
          mul_nonneg (abs_nonneg _) hZpos.le
        calc (C₀ * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)))) ^ n
            ≤ |(C₀ * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)))) ^ n| := le_abs_self _
          _ = (|C₀| * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)))) ^ n := by
              rw [abs_pow, abs_mul, abs_of_pos hZpos]
          _ ≤ _ := by
              first
              | exact pow_le_pow_left h0 hle n
              | exact pow_le_pow_left₀ h0 hle n

theorem t_LatticeSumsJoint : LatticeSumsJoint := by
  intro hBS
  obtain ⟨C, hC1, hC⟩ := t_BoxSumLattice hBS
  refine ⟨C, hC1, ?_⟩
  intro E W _ _ _ D e aaD aaL Θ a hP hK ha hΘ hI
  have hcard : Fintype.card (InfinitePlace E) = D.f := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hΘ0 : 0 < Θ := by linarith
  have key : ∀ (aa : FractionalIdeal (𝓞 E)⁰ E) (large₂ : AddSubgroup E) (z : Fin D.f → ℝ) (c : ℝ),
      aa ≠ 0 → (∀ l ∈ large₂, l ∈ aa) → (∀ v, 0 ≤ z v) → 0 ≤ c → c ≤ a →
      ∏ v, z v ≤ (c / Θ) ^ D.f * √(FractionalIdeal.absNorm aa : ℝ) →
      ∀ L : Finset E, (∀ l ∈ L, l ∈ large₂ ∧ l ≠ 0) →
        ∑ l ∈ L, D.maj z l ≤ (C * a ^ ((D.K : ℝ) - 5 / 2) * Θ ^ (-((D.K : ℝ) - 5 / 2))) ^ D.f := by
    intro aa large₂ z c haa hLg hz hc hca hprod L hL
    have hre : ∏ w, z (e.symm w) = ∏ v, z v := Fintype.prod_equiv e.symm _ _ (fun w => rfl)
    have hcd : c / Θ ≤ a / Θ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hca (inv_nonneg.mpr hΘ0.le)
    have hle : (c / Θ) ^ D.f ≤ (a / Θ) ^ D.f := by
      first
      | exact pow_le_pow_left (div_nonneg hc hΘ0.le) hcd _
      | exact pow_le_pow_left₀ (div_nonneg hc hΘ0.le) hcd _
    have hprod' : ∏ w, z (e.symm w) ≤
        (a / Θ) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm aa : ℝ) := by
      rw [hre, hcard]
      exact hprod.trans (mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _))
    have hLS0 := hC E aa large₂ (fun w => z (e.symm w)) D.K Θ a haa hLg (fun w => hz _) hK ha hΘ hprod'
    unfold TA.LatSum at hLS0
    have hLS := hLS0.2 L hL
    rw [hcard] at hLS
    calc ∑ l ∈ L, D.maj z l = ∑ l ∈ L, prof (fun w => z (e.symm w)) D.K l :=
          Finset.sum_congr rfl (fun l _ => t_MajIsProf E W D e hP z l)
      _ ≤ _ := hLS
  unfold IdealSizes at hI
  unfold TB.Data.LatticeSums
  constructor
  · intro i hi1 hi2 L hL
    obtain ⟨h1, h2, h3, h4⟩ := hI.1 i hi1 hi2
    exact key (aaD i) (D.Lad i) (D.szD i) 1 h1 h2 h3 zero_le_one ha h4 L hL
  · intro i s hs1 hs2 hi hne L hL
    obtain ⟨h1, h2, h3, h4⟩ := hI.2 (i - s + 1) s (by omega) hs1 (by omega) (by omega)
    exact key (aaL (i - s + 1) s) (D.Lap (i - s + 1) s) (D.szL (i - s + 1) s) a h1 h2 h3
      (by linarith) le_rfl h4 L hL

theorem t_LevelSizesJoint : LevelSizesJoint := by
  intro C₁ C₄ hC₁ hC₄ E W _ D Θ hK hf hΘ hav hszD hszL he hSB hLS i hi
  have hΘpos : 0 < Θ := by linarith
  have hi' := Finset.mem_Icc.mp hi
  have hex1 : (1 : ℝ) ≤ (D.K : ℝ) - 5 / 2 := by
    have : (4 : ℝ) ≤ D.K := by exact_mod_cast hK
    linarith
  have hΘe : Θ ^ (-((D.K : ℝ) - 5 / 2)) ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hΘepos : 0 < Θ ^ (-((D.K : ℝ) - 5 / 2)) := Real.rpow_pos_of_pos hΘpos _
  have hMpos : 0 < max (3 * C₁) (2 * C₄) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  set X : ℝ := C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) with hX
  set M : ℝ := max (3 * C₁) (2 * C₄) with hM
  set Y : ℝ := M * Θ ^ (-((D.K : ℝ) - 5 / 2)) with hY
  have hX0 : 0 ≤ X := mul_nonneg (by linarith) hΘepos.le
  have hY0 : 0 ≤ Y := mul_nonneg hMpos.le hΘepos.le
  have h3X : 3 * X ≤ 1 := by
    have h1 : 3 * C₁ * Θ⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      first
      | exact (div_le_one hΘpos).mpr hΘ
      | exact (div_le_one₀ hΘpos).mpr hΘ
    have h2 : 3 * C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) ≤ 3 * C₁ * Θ⁻¹ :=
      mul_le_mul_of_nonneg_left hΘe (by linarith)
    calc 3 * X = 3 * C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) := by rw [hX]; ring
      _ ≤ 1 := h2.trans h1
  have h3XM : 3 * X ≤ Y := by
    calc 3 * X = 3 * C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) := by rw [hX]; ring
      _ ≤ Y := mul_le_mul_of_nonneg_right (le_max_left _ _) hΘepos.le
  have hcard : (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f = (3 * X) ^ D.f := by
    first
    | (simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, mul_pow]; done)
    | (simp [Fintype.card_fun, mul_pow]; done)
    | (rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, mul_pow]; push_cast; ring)
  have hA1 : (3 * X) ^ D.f ≤ 1 := by
    first
    | exact pow_le_one₀ (by linarith) h3X
    | exact pow_le_one _ (by linarith) h3X
  have hA2 : (3 * X) ^ D.f ≤ Y ^ D.f := by
    first
    | exact pow_le_pow_left (by linarith) h3XM _
    | exact pow_le_pow_left₀ (by linarith) h3XM _
  have hB2 : X ^ D.f ≤ Y ^ D.f := by
    have hXY : X ≤ Y := by linarith
    first
    | exact pow_le_pow_left hX0 hXY _
    | exact pow_le_pow_left₀ hX0 hXY _
  unfold TB.Data.LatticeSums at hLS
  unfold TB.Data.SizesBelow at hSB
  have hmaj : ∀ (z : Fin D.f → ℝ), (∀ v, 0 ≤ z v) → ∀ l, 0 ≤ D.maj z l := by
    intro z hz l
    unfold TB.Data.maj
    exact Finset.prod_nonneg (fun v _ => le_min zero_le_one
      (pow_nonneg (div_nonneg (hz v) (hav v l)) _))
  unfold TA.LevelSizes TA.LatSum
  try beta_reduce
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact hmaj _ (hszD i)
  · intro S hS
    exact hLS.1 i hi'.1 hi'.2 S hS
  · intro s hs hne
    have hs' := Finset.mem_Icc.mp hs
    exact ⟨hmaj _ (hszL _ _), fun S hS => hLS.2 i s hs'.1 hs'.2 hi'.2 hne S hS⟩
  · exact pow_nonneg hX0 _
  · show (1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f) * (1 + X ^ D.f) ≤
      (1 + Y ^ D.f) ^ 2
    rw [hcard, sq]
    have hx0 := pow_nonneg hX0 D.f
    have hy0 := pow_nonneg hY0 D.f
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  · intro s hs
    have hs' := Finset.mem_Icc.mp hs
    have hvol0 : ∀ s', 0 ≤ D.vol (i - s + 1) s' := fun s' => hSB.1 _ _
    have hP0 : 0 ≤ ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' :=
      Finset.prod_nonneg (fun s' _ => hvol0 s')
    have hC4p : 0 ≤ C₄ ^ (D.f * s) := pow_nonneg (by linarith) _
    refine ⟨mul_nonneg hC4p hP0, ?_⟩
    have hPQ : ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by
      calc ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ ∏ s' ∈ Ico 1 s, ((Θ ^ D.f)⁻¹) ^ 2 := by
            apply Finset.prod_le_prod (fun s' _ => hvol0 s')
            intro s' hs''
            have h5 := Finset.mem_Ico.mp hs''
            exact hSB.2 _ _ (by omega) h5.1 (by omega)
        _ = (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by rw [Finset.prod_const, Nat.card_Ico]
    have hQ0 : 0 ≤ (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by positivity
    have hAe : 1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f ≤ 2 := by
      rw [hcard]
      linarith
    have hBe : 1 + D.e i ≤ 2 := by linarith [(he i hi'.1 hi'.2).2]
    have hB0 : 0 ≤ 1 + D.e i := by linarith [(he i hi'.1 hi'.2).1]
    have hkey : 4 * C₄ ^ (D.f * s) ≤ (M ^ D.f) ^ (2 * (s - 1)) := by
      have h2C : 2 * C₄ ≤ M := le_max_right _ _
      have h22 : 2 ≤ 2 * (s - 1) := by omega
      have hexp : 2 ≤ D.f * (2 * (s - 1)) := by
        have h6 := Nat.mul_le_mul hf h22
        simpa using h6
      have hexp2 : D.f * s ≤ D.f * (2 * (s - 1)) := Nat.mul_le_mul le_rfl (by omega)
      have h4 : (4 : ℝ) ≤ 2 ^ (D.f * (2 * (s - 1))) := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (D.f * (2 * (s - 1))) := by
            first
            | exact pow_le_pow_right₀ (by norm_num) hexp
            | exact pow_le_pow_right (by norm_num) hexp
      have hc : C₄ ^ (D.f * s) ≤ C₄ ^ (D.f * (2 * (s - 1))) := by
        first
        | exact pow_le_pow_right₀ hC₄ hexp2
        | exact pow_le_pow_right hC₄ hexp2
      calc 4 * C₄ ^ (D.f * s) ≤ 2 ^ (D.f * (2 * (s - 1))) * C₄ ^ (D.f * (2 * (s - 1))) :=
            mul_le_mul h4 hc (pow_nonneg (by linarith) _) (by positivity)
        _ = (2 * C₄) ^ (D.f * (2 * (s - 1))) := by rw [mul_pow]
        _ ≤ M ^ (D.f * (2 * (s - 1))) := by
            first
            | exact pow_le_pow_left (by linarith) h2C _
            | exact pow_le_pow_left₀ (by linarith) h2C _
        _ = (M ^ D.f) ^ (2 * (s - 1)) := by rw [pow_mul]
    have hRHS : ((M / Θ) ^ D.f) ^ (2 * (s - 1)) =
        (M ^ D.f) ^ (2 * (s - 1)) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by
      rw [div_pow, div_eq_mul_inv, mul_pow, ← pow_mul ((Θ ^ D.f)⁻¹) 2 (s - 1)]
    show (1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f) * (1 + D.e i) *
        (C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') ≤ ((M / Θ) ^ D.f) ^ (2 * (s - 1))
    rw [hRHS]
    calc (1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f) * (1 + D.e i) *
          (C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s')
        ≤ 2 * 2 * (C₄ ^ (D.f * s) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1)) :=
          mul_le_mul (mul_le_mul hAe hBe hB0 (by norm_num)) (mul_le_mul_of_nonneg_left hPQ hC4p)
            (mul_nonneg hC4p hP0) (by norm_num)
      _ = (4 * C₄ ^ (D.f * s)) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by ring
      _ ≤ (M ^ D.f) ^ (2 * (s - 1)) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) :=
          mul_le_mul_of_nonneg_right hkey hQ0

theorem t_LevelSizesJointMean : LevelSizesJointMean := by
  intro C₁ C₄ hC₁ hC₄ E W _ D Θ hK hf hΘ hav hszD hszL he hSB hLS i hi
  have hΘpos : 0 < Θ := by linarith
  have hi' := Finset.mem_Icc.mp hi
  have hex1 : (1 : ℝ) ≤ (D.K : ℝ) - 5 / 2 := by
    have : (4 : ℝ) ≤ D.K := by exact_mod_cast hK
    linarith
  have hΘe : Θ ^ (-((D.K : ℝ) - 5 / 2)) ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hΘepos : 0 < Θ ^ (-((D.K : ℝ) - 5 / 2)) := Real.rpow_pos_of_pos hΘpos _
  have hMpos : 0 < max (3 * C₁) (2 * C₄) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  set X : ℝ := C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) with hX
  set M : ℝ := max (3 * C₁) (2 * C₄) with hM
  set Y : ℝ := M * Θ ^ (-((D.K : ℝ) - 5 / 2)) with hY
  have hX0 : 0 ≤ X := mul_nonneg (by linarith) hΘepos.le
  have hY0 : 0 ≤ Y := mul_nonneg hMpos.le hΘepos.le
  have h3X : 3 * X ≤ 1 := by
    have h1 : 3 * C₁ * Θ⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      first
      | exact (div_le_one hΘpos).mpr hΘ
      | exact (div_le_one₀ hΘpos).mpr hΘ
    have h2 : 3 * C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) ≤ 3 * C₁ * Θ⁻¹ :=
      mul_le_mul_of_nonneg_left hΘe (by linarith)
    calc 3 * X = 3 * C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) := by rw [hX]; ring
      _ ≤ 1 := h2.trans h1
  have h3XM : 3 * X ≤ Y := by
    calc 3 * X = 3 * C₁ * Θ ^ (-((D.K : ℝ) - 5 / 2)) := by rw [hX]; ring
      _ ≤ Y := mul_le_mul_of_nonneg_right (le_max_left _ _) hΘepos.le
  have hcard : (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f = (3 * X) ^ D.f := by
    first
    | (simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, mul_pow]; done)
    | (simp [Fintype.card_fun, mul_pow]; done)
    | (rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, mul_pow]; push_cast; ring)
  have hA1 : (3 * X) ^ D.f ≤ 1 := by
    first
    | exact pow_le_one₀ (by linarith) h3X
    | exact pow_le_one _ (by linarith) h3X
  have hA2 : (3 * X) ^ D.f ≤ Y ^ D.f := by
    first
    | exact pow_le_pow_left (by linarith) h3XM _
    | exact pow_le_pow_left₀ (by linarith) h3XM _
  have hB2 : 2 ^ D.f * X ^ D.f ≤ Y ^ D.f := by
    rw [← mul_pow]
    have h2X : 2 * X ≤ Y := by linarith
    first
    | exact pow_le_pow_left (by linarith) h2X _
    | exact pow_le_pow_left₀ (by linarith) h2X _
  unfold TB.Data.LatticeSums at hLS
  unfold TB.Data.SizesBelow at hSB
  have hmaj : ∀ (z : Fin D.f → ℝ), (∀ v, 0 ≤ z v) → ∀ l, 0 ≤ D.maj z l := by
    intro z hz l
    unfold TB.Data.maj
    exact Finset.prod_nonneg (fun v _ => le_min zero_le_one
      (pow_nonneg (div_nonneg (hz v) (hav v l)) _))
  unfold TA.LevelSizes TA.LatSum
  try beta_reduce
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro l
    exact mul_nonneg (by positivity) (hmaj _ (hszD i) l)
  · intro S hS
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hLS.1 i hi'.1 hi'.2 S hS) (by positivity)
  · intro s hs hne
    have hs' := Finset.mem_Icc.mp hs
    exact ⟨hmaj _ (hszL _ _), fun S hS => hLS.2 i s hs'.1 hs'.2 hi'.2 hne S hS⟩
  · exact pow_nonneg hX0 _
  · show (1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f) * (1 + 2 ^ D.f * X ^ D.f) ≤
      (1 + Y ^ D.f) ^ 2
    rw [hcard, sq]
    have hx0 := pow_nonneg hX0 D.f
    have hy0 := pow_nonneg hY0 D.f
    have h20 : (0 : ℝ) ≤ 2 ^ D.f * X ^ D.f := mul_nonneg (pow_nonneg zero_le_two D.f) hx0
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  · intro s hs
    have hs' := Finset.mem_Icc.mp hs
    have hvol0 : ∀ s', 0 ≤ D.vol (i - s + 1) s' := fun s' => hSB.1 _ _
    have hP0 : 0 ≤ ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' :=
      Finset.prod_nonneg (fun s' _ => hvol0 s')
    have hC4p : 0 ≤ C₄ ^ (D.f * s) := pow_nonneg (by linarith) _
    refine ⟨mul_nonneg hC4p hP0, ?_⟩
    have hPQ : ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by
      calc ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ ∏ s' ∈ Ico 1 s, ((Θ ^ D.f)⁻¹) ^ 2 := by
            apply Finset.prod_le_prod (fun s' _ => hvol0 s')
            intro s' hs''
            have h5 := Finset.mem_Ico.mp hs''
            exact hSB.2 _ _ (by omega) h5.1 (by omega)
        _ = (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by rw [Finset.prod_const, Nat.card_Ico]
    have hQ0 : 0 ≤ (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by positivity
    have hAe : 1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f ≤ 2 := by
      rw [hcard]
      linarith
    have hBe : 1 + D.e i ≤ 2 := by linarith [(he i hi'.1 hi'.2).2]
    have hB0 : 0 ≤ 1 + D.e i := by linarith [(he i hi'.1 hi'.2).1]
    have hkey : 4 * C₄ ^ (D.f * s) ≤ (M ^ D.f) ^ (2 * (s - 1)) := by
      have h2C : 2 * C₄ ≤ M := le_max_right _ _
      have h22 : 2 ≤ 2 * (s - 1) := by omega
      have hexp : 2 ≤ D.f * (2 * (s - 1)) := by
        have h6 := Nat.mul_le_mul hf h22
        simpa using h6
      have hexp2 : D.f * s ≤ D.f * (2 * (s - 1)) := Nat.mul_le_mul le_rfl (by omega)
      have h4 : (4 : ℝ) ≤ 2 ^ (D.f * (2 * (s - 1))) := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (D.f * (2 * (s - 1))) := by
            first
            | exact pow_le_pow_right₀ (by norm_num) hexp
            | exact pow_le_pow_right (by norm_num) hexp
      have hc : C₄ ^ (D.f * s) ≤ C₄ ^ (D.f * (2 * (s - 1))) := by
        first
        | exact pow_le_pow_right₀ hC₄ hexp2
        | exact pow_le_pow_right hC₄ hexp2
      calc 4 * C₄ ^ (D.f * s) ≤ 2 ^ (D.f * (2 * (s - 1))) * C₄ ^ (D.f * (2 * (s - 1))) :=
            mul_le_mul h4 hc (pow_nonneg (by linarith) _) (by positivity)
        _ = (2 * C₄) ^ (D.f * (2 * (s - 1))) := by rw [mul_pow]
        _ ≤ M ^ (D.f * (2 * (s - 1))) := by
            first
            | exact pow_le_pow_left (by linarith) h2C _
            | exact pow_le_pow_left₀ (by linarith) h2C _
        _ = (M ^ D.f) ^ (2 * (s - 1)) := by rw [pow_mul]
    have hRHS : ((M / Θ) ^ D.f) ^ (2 * (s - 1)) =
        (M ^ D.f) ^ (2 * (s - 1)) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by
      rw [div_pow, div_eq_mul_inv, mul_pow, ← pow_mul ((Θ ^ D.f)⁻¹) 2 (s - 1)]
    show (1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f) * (1 + D.e i) *
        (C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') ≤ ((M / Θ) ^ D.f) ^ (2 * (s - 1))
    rw [hRHS]
    calc (1 + (Fintype.card (Fin D.f → Fin 3) : ℝ) * X ^ D.f) * (1 + D.e i) *
          (C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s')
        ≤ 2 * 2 * (C₄ ^ (D.f * s) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1)) :=
          mul_le_mul (mul_le_mul hAe hBe hB0 (by norm_num)) (mul_le_mul_of_nonneg_left hPQ hC4p)
            (mul_nonneg hC4p hP0) (by norm_num)
      _ = (4 * C₄ ^ (D.f * s)) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) := by ring
      _ ≤ (M ^ D.f) ^ (2 * (s - 1)) * (((Θ ^ D.f)⁻¹) ^ 2) ^ (s - 1) :=
          mul_le_mul_of_nonneg_right hkey hQ0

theorem t_NuIndex : NuIndex := by
  intro r i s _ h2
  simp only [S6.nuBlock]
  omega

lemma rd_pos (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by
  unfold S6.rd
  apply Real.rpow_pos_of_pos
  have h : discr E ≠ 0 := NumberField.discr_ne_zero E
  exact_mod_cast abs_pos.mpr h

lemma idl_ne_zero (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ)
    (hg : 0 < g) : S6.idl E g k ν ≠ 0 := by
  intro h
  have h1 := hN E g k ν hg
  rw [h, map_zero, Rat.cast_zero, Real.sqrt_zero] at h1
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hz1 : (0 : ℝ) < (g : ℝ) ^ k := zpow_pos hg' k
  have hz2 : (0 : ℝ) < S6.rd E ^ ν := zpow_pos (rd_pos E) ν
  have hpos : 0 < ((g : ℝ) ^ k * S6.rd E ^ ν) ^ S6.deg E := pow_pos (mul_pos hz1 hz2) _
  linarith

lemma sqrt_idl (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (μ : ℤ)
    (hg : 0 < g) : √(FractionalIdeal.absNorm (S6.idl E g (-1) (-μ)) : ℝ) =
      (((g : ℝ) * S6.rd E ^ μ) ^ S6.deg E)⁻¹ := by
  rw [hN E g (-1) (-μ) hg]
  simp only [zpow_neg, zpow_one, mul_pow, inv_pow, mul_inv]

theorem t_BlockLattices : BlockLattices := by
  intro hLG _ hN E _ _ _ hU g r b s hg
  have F1 := hLG E hU g (S6.nuBlock r b 1) 1 hg
  have Fs := hLG E hU g (S6.nuBlock r b s) s hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    exact F1.2.2.2.2.1 hl
  · intro l hl
    exact Fs.2.2.2.2.1 hl
  · intro l hl
    exact Fs.2.2.2.2.2.2.1 hl
  · exact idl_ne_zero hN E g (-1) (-(S6.nuBlock r b s + 1)) hg
  · exact idl_ne_zero hN E g (-1) (-(S6.nuBlock r b s)) hg
  · simp only [S6.liftIdl, S6.dualIdl, S6.nuBlock]
    congr 1
    push_cast
    ring
  · have hν : S6.nuBlock r b s + 1 = (2 * r + 4 : ℤ) - 2 * b - s := by
      simp only [S6.nuBlock]
      ring
    rw [show S6.dualIdl E g (S6.nuBlock r b s) = S6.idl E g (-1) (-(S6.nuBlock r b s + 1)) from rfl,
      sqrt_idl hN E g _ hg, hν]
  · rw [show S6.liftIdl E g (S6.nuBlock r b s) = S6.idl E g (-1) (-(S6.nuBlock r b s)) from rfl,
      sqrt_idl hN E g _ hg]
    try rfl

theorem t_EmbFacts : EmbFacts := by
  intro E _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
    have h' : w.embedding a = w.embedding b := by
      simpa [cemb] using congrArg (fun x : CV E => x w) h
    exact w.embedding.injective h'
  · constructor
    · intro x y h
      ext w
      simpa [coord] using congrFun h w
    · intro f
      exact ⟨WithLp.toLp 2 f, by funext w; simp [coord]⟩
  · intro t w
    simp [coord, cemb, InfinitePlace.norm_embedding_eq]
  · intro c t
    rfl
  · intro g c l w
    simp [coord, dm, InfinitePlace.norm_embedding_eq]
    left
    rw [abs_div, abs_mul, Nat.abs_cast, abs_two]

section Euclid

open NumberField.mixedEmbedding MeasureTheory

open scoped Classical

noncomputable section

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem isC (w : InfinitePlace E) : w.IsComplex := IsTotallyComplex.isComplex w

local instance isEmptyReal : IsEmpty {w : InfinitePlace E // w.IsReal} :=
  ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 (isC E w.1)) w.2⟩

variable {E} in
theorem mext {y z : euclidean.mixedSpace E} (h : ∀ w, y.snd w = z.snd w) : y = z := by
  have h1 : y.fst = z.fst := by
    ext w
    exact isEmptyElim w
  have h2 : y.snd = z.snd := by
    ext w
    exact h w
  first
  | exact WithLp.prod_ext h1 h2
  | exact WithLp.ofLp_injective 2 (Prod.ext h1 h2)
  | exact WithLp.ofLp_injective (Prod.ext h1 h2)
  | (apply WithLp.prod_ext <;> assumption)
  | (rcases y with ⟨y⟩; rcases z with ⟨z⟩; exact congrArg (WithLp.toLp 2) (Prod.ext h1 h2))

def phiL : CV E ≃ₗ[ℝ] euclidean.mixedSpace E where
  toFun x := WithLp.toLp 2 (0, WithLp.toLp 2 (fun w : {w : InfinitePlace E // w.IsComplex} => x w.1))
  invFun y := WithLp.toLp 2 (fun w : InfinitePlace E => y.snd ⟨w, isC E w⟩)
  map_add' x y := mext fun w => by simp
  map_smul' c x := mext fun w => by simp
  left_inv x := by ext w; simp
  right_inv y := mext fun w => by simp

theorem phi_norm (x : CV E) : ‖phiL E x‖ = ‖x‖ := by
  have key : ‖phiL E x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq (phiL E x).snd,
      EuclideanSpace.norm_sq_eq x]
    have hf : (phiL E x).fst = 0 := rfl
    rw [hf, norm_zero, zero_pow two_ne_zero, zero_add]
    exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv (isC E)) _ _ (fun w => rfl)
  rw [← Real.sqrt_sq (norm_nonneg (phiL E x)), key, Real.sqrt_sq (norm_nonneg x)]

def phi : CV E ≃ₗᵢ[ℝ] euclidean.mixedSpace E := ⟨phiL E, phi_norm E⟩

def ee : CV E ≃L[ℝ] mixedSpace E := (phi E).toContinuousLinearEquiv.trans (euclidean.toMixed E)

theorem ee_mp : MeasurePreserving (ee E) := by
  have h : ⇑(ee E) = ⇑(euclidean.toMixed E) ∘ ⇑(phi E) := rfl
  rw [h]
  first
  | exact (euclidean.volumePreserving_toMixed E).comp (phi E).measurePreserving
  | exact euclidean.volumePreserving_toMixed.comp (phi E).measurePreserving
  | exact (euclidean.volumePreserving_toMixed E).comp (LinearIsometryEquiv.measurePreserving (phi E))

theorem ee_cemb (t : E) : ee E (cemb E t) = mixedEmbedding E t := by
  ext w
  · exact isEmptyElim w
  · rfl

theorem ee_semb (c : ℝ) (t : E) : ee E (semb E c t) = c • mixedEmbedding E t := by
  have h : semb E c t = c • cemb E t := rfl
  rw [h, map_smul, ee_cemb]

theorem eLat_eq (L : Submodule ℤ E) (c : ℝ) :
    eLat E L c = ZLattice.comap ℝ (S6.frameLat E L c) (ee E).toLinearMap := by
  ext v
  simp only [eLat, S6.frameLat, ZLattice.comap, Submodule.mem_map, Submodule.mem_comap]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨mixedEmbedding E t, ⟨t, ht, rfl⟩, (ee_semb E c t).symm⟩
  · rintro ⟨u, ⟨t, ht, rfl⟩, h⟩
    refine ⟨t, ht, (ee E).injective ?_⟩
    exact (ee_semb E c t).trans h

theorem t_EuclidFrame : EuclidFrame := by
  intro E _ _ _ L c hd hs
  haveI : IsZLattice ℝ (S6.frameLat E L c) := ⟨hs⟩
  rw [eLat_eq E L c]
  refine ⟨?_, ?_, ?_⟩
  · infer_instance
  · exact IsZLattice.span_top
  · exact ZLattice.covolume_comap _ _ _ (ee_mp E)

end

end Euclid

end Formalism.FourierDecayAlt.P.Jx2

namespace Formalism.FourierDecayAlt.P

theorem lattice_sums_joint : Formalism.FourierDecayAlt.J.LatticeSumsJoint := Jx2.t_LatticeSumsJoint

theorem level_sizes_joint : Formalism.FourierDecayAlt.J.LevelSizesJoint := Jx2.t_LevelSizesJoint

theorem level_sizes_joint_mean : Formalism.FourierDecayAlt.J.LevelSizesJointMean := Jx2.t_LevelSizesJointMean

theorem nu_index : Formalism.FourierDecayAlt.J.NuIndex := Jx2.t_NuIndex

theorem block_lattices : Formalism.FourierDecayAlt.J.BlockLattices := Jx2.t_BlockLattices

theorem embedding_facts : Formalism.FourierDecayAlt.J.EmbFacts := Jx2.t_EmbFacts

theorem euclidean_frame : Formalism.FourierDecayAlt.J.EuclidFrame := Jx2.t_EuclidFrame

end Formalism.FourierDecayAlt.P
