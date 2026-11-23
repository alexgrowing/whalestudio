import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe

open Complex MeasureTheory

namespace GlobalTheory.CharFamily

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem seminorm_mul_le (c : E → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (h g : SchwartzMap E ℂ)
    (hg : ∀ x, g x = c x * h x) (k n m : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hcb : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i c x‖ ≤ M * (1 + ‖x‖) ^ m) :
    SchwartzMap.seminorm ℂ k n g ≤ 2 ^ n * M *
      (2 ^ (k + m) * ((Finset.Iic (k + m, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) h) := by
  set S := 2 ^ (k + m) * ((Finset.Iic (k + m, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) h
    with hS
  have hS0 : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
  refine SchwartzMap.seminorm_le_bound ℂ k n g (by positivity) fun x => ?_
  have hg' : (⇑g) = fun x => c x * h x := funext hg
  rw [hg']
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) hc (h.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖)
        ≤ (n.choose i : ℝ) * (M * S) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := hcb i hi' x
    have h2 : (1 + ‖x‖) ^ (k + m) * ‖iteratedFDeriv ℝ (n - i) h x‖ ≤ S :=
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (k + m, n)) le_rfl (Nat.sub_le n i) h x
    have h5 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
    have hc0 : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖)
        = (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ i c x‖ *
            ‖iteratedFDeriv ℝ (n - i) h x‖) := by ring
      _ ≤ (n.choose i : ℝ) * ((1 + ‖x‖) ^ k * (M * (1 + ‖x‖) ^ m) *
            ‖iteratedFDeriv ℝ (n - i) h x‖) := by gcongr
      _ = (n.choose i : ℝ) * (M * ((1 + ‖x‖) ^ (k + m) * ‖iteratedFDeriv ℝ (n - i) h x‖)) := by
            ring
      _ ≤ (n.choose i : ℝ) * (M * S) := by gcongr
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => c y * h y) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i c x‖ * ‖iteratedFDeriv ℝ (n - i) h x‖) := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M * S) := Finset.sum_le_sum hterm
    _ = 2 ^ n * M * S := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this]; ring

theorem contDiff_char (L : E →L[ℝ] ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => Complex.exp (I * (L x : ℂ))) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (I * (y : ℂ))) := by fun_prop
  exact hc.comp L.contDiff

theorem norm_iteratedFDeriv_char_le (L : E →L[ℝ] ℝ) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x : E => Complex.exp (I * (L x : ℂ))) x‖ ≤ ‖L‖ ^ i := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) := by
    fun_prop
  have e : (fun x : E => Complex.exp (I * (L x : ℂ)))
      = (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) ∘ ⇑L := by
    funext x; simp
  rw [e, L.iteratedFDeriv_comp_right hc x (i := i) (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ i (fun y : ℝ => (1 : ℂ) * Complex.exp (I * (y : ℂ))) (L x)‖
          * ∏ _j : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖L‖ ^ i := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
        have hexp : I * ((L x : ℝ) : ℂ) = ((L x : ℝ) : ℂ) * I := by ring
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_mul, norm_pow, Complex.norm_I]
        simp

theorem norm_iteratedFDeriv_char_sub_one_le (L : E →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x : E => Complex.exp (I * (L x : ℂ)) - 1) x‖
      ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg L
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  have hc : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : ℝ => (1 : ℂ) * Complex.exp (I * y) + 0 * y + (-1)) := by fun_prop
  have e : (fun x : E => Complex.exp (I * (L x : ℂ)) - 1)
      = (fun y : ℝ => (1 : ℂ) * Complex.exp (I * y) + 0 * y + (-1)) ∘ ⇑L := by
    funext x; simp; ring
  rw [e, L.iteratedFDeriv_comp_right hc x (i := i) (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  cases i with
  | zero =>
    rw [iteratedDeriv_zero, pow_zero, mul_one]
    have h0 : (1 : ℂ) * Complex.exp (I * ((L x : ℝ) : ℂ)) + 0 * ((L x : ℝ) : ℂ) + (-1)
        = Complex.exp (((L x : ℝ) : ℂ) * I) - 1 := by ring_nf
    simp only [h0]
    calc _ ≤ 2 * |L x| := GlobalTheory.CharFormDeriv.norm_cexp_mul_I_sub_one_le (L x)
      _ ≤ 2 * (‖L‖ * ‖x‖) := by gcongr; rw [← Real.norm_eq_abs]; exact L.le_opNorm x
      _ ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by nlinarith
  | succ j =>
    rw [iteratedDeriv_succ', GlobalTheory.CharFormDeriv.deriv_affine_cexp]
    have hd : (fun y : ℝ => (1 : ℂ) * I * Complex.exp (I * y) + 0)
        = fun y : ℝ => I * Complex.exp (I * y) := by funext y; ring
    rw [hd, GlobalTheory.CharFormDeriv.iteratedDeriv_const_mul_cexp]
    have hexp : I * ((L x : ℝ) : ℂ) = ((L x : ℝ) : ℂ) * I := by ring
    rw [norm_mul, norm_mul, hexp, Complex.norm_exp_ofReal_mul_I, norm_pow, Complex.norm_I]
    simp only [one_pow, mul_one, one_mul]
    calc ‖L‖ ^ (j + 1) ≤ ‖L‖ ^ 1 := pow_le_pow_of_le_one hL0 hL (by omega)
      _ ≤ 2 * ‖L‖ * (1 + ‖x‖) ^ 1 := by nlinarith

theorem one_add_pow_le (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  have han : 0 ≤ a ^ n := pow_nonneg ha n
  rcases le_total a 1 with h | h
  · have : (1 + a) ^ n ≤ 2 ^ n := by gcongr; linarith
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]
  · have : (1 + a) ^ n ≤ (2 * a) ^ n := by gcongr; linarith
    rw [mul_pow] at this
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]

theorem charMul_family : ∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P →L[ℝ] E →L[ℝ] ℝ) (f : SchwartzMap E ℂ), ∃ Φ : P → SchwartzMap E ℂ,
    (∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x) ∧ Continuous Φ ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n) := by
  intro E P _ _ _ _ A f
  have htg : ∀ L : E →L[ℝ] ℝ,
      Function.HasTemperateGrowth (fun x : E => Complex.exp (I * (L x : ℂ))) := fun L => by
    simpa using GlobalTheory.CharFormDeriv.hasTemperateGrowth_char L 1
  let Φ : P → SchwartzMap E ℂ := fun ξ =>
    SchwartzMap.smulLeftCLM ℂ (fun x : E => Complex.exp (I * (A ξ x : ℂ))) f
  have hΦ : ∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x := fun ξ x => by
    simp only [Φ, SchwartzMap.smulLeftCLM_apply_apply (htg (A ξ)), smul_eq_mul]
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun ζ => ?_
    unfold ContinuousAt
    rw [(schwartz_withSeminorms ℂ E ℂ).tendsto_nhds Φ (Φ ζ)]
    rintro ⟨k, n⟩ ε hε
    set K := 2 * 2 ^ n * (2 ^ (k + 1) *
      ((Finset.Iic (k + 1, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) (Φ ζ)) with hK
    have hK0 : 0 ≤ K := mul_nonneg (by positivity) (mul_nonneg (by positivity) (apply_nonneg _ _))
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
    set m := min 1 (ε / (K + 1)) with hm
    have hm0 : 0 < m := lt_min one_pos (div_pos hε (by linarith))
    have hδ : 0 < m / (‖A‖ + 1) := div_pos hm0 (by linarith)
    filter_upwards [Metric.ball_mem_nhds ζ hδ] with η hη
    rw [Metric.mem_ball, dist_eq_norm] at hη
    show SchwartzMap.seminorm ℂ k n (Φ η - Φ ζ) < ε
    set L := A (η - ζ) with hLdef
    have hLle : ‖L‖ ≤ ‖A‖ * ‖η - ζ‖ := A.le_opNorm _
    have hLm : ‖L‖ < m := by
      calc ‖L‖ ≤ ‖A‖ * ‖η - ζ‖ := hLle
        _ ≤ (‖A‖ + 1) * ‖η - ζ‖ := by gcongr; linarith
        _ < (‖A‖ + 1) * (m / (‖A‖ + 1)) := by gcongr
        _ = m := by field_simp
    have hL1 : ‖L‖ ≤ 1 := (lt_of_lt_of_le hLm (min_le_left _ _)).le
    have hLε : ‖L‖ < ε / (K + 1) := lt_of_lt_of_le hLm (min_le_right _ _)
    have hpt : ∀ x, (Φ η - Φ ζ) x = (Complex.exp (I * (L x : ℂ)) - 1) * Φ ζ x := fun x => by
      have hs : A η x = L x + A ζ x := by simp [hLdef, map_sub]
      rw [SchwartzMap.sub_apply, hΦ, hΦ, hs]
      push_cast
      rw [mul_add, Complex.exp_add]
      ring
    have hb := seminorm_mul_le (fun x : E => Complex.exp (I * (L x : ℂ)) - 1)
      ((contDiff_char L).sub contDiff_const) (Φ ζ) (Φ η - Φ ζ) hpt k n 1 (2 * ‖L‖)
      (by positivity) (fun i _ x => norm_iteratedFDeriv_char_sub_one_le L hL1 i x)
    calc SchwartzMap.seminorm ℂ k n (Φ η - Φ ζ) ≤ ‖L‖ * K := by rw [hK]; linarith [hb]
      _ ≤ ‖L‖ * (K + 1) := by gcongr; linarith
      _ < ε / (K + 1) * (K + 1) := by gcongr
      _ = ε := by field_simp
  · intro k n
    set S := 2 ^ (k + 0) * ((Finset.Iic (k + 0, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) f
      with hS
    have hS0 : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
    refine ⟨2 ^ n * ((1 + ‖A‖) ^ n * 2 ^ n) * S, fun ξ => ?_⟩
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
    have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
    set L := A ξ with hLdef
    have hL0 : 0 ≤ ‖L‖ := norm_nonneg L
    have hb := seminorm_mul_le (fun x : E => Complex.exp (I * (L x : ℂ))) (contDiff_char L) f (Φ ξ)
      (hΦ ξ) k n 0 ((1 + ‖L‖) ^ n) (by positivity) (fun i hi x => by
        rw [pow_zero, mul_one]
        calc _ ≤ ‖L‖ ^ i := norm_iteratedFDeriv_char_le L i x
          _ ≤ (1 + ‖L‖) ^ i := by gcongr; linarith
          _ ≤ (1 + ‖L‖) ^ n := pow_le_pow_right₀ (by linarith) hi)
    have h1 : (1 + ‖L‖) ^ n ≤ (1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n)) := by
      calc (1 + ‖L‖) ^ n ≤ ((1 + ‖A‖) * (1 + ‖ξ‖)) ^ n := by
            gcongr
            have := A.le_opNorm ξ
            nlinarith
        _ = (1 + ‖A‖) ^ n * (1 + ‖ξ‖) ^ n := mul_pow _ _ _
        _ ≤ (1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n)) := by
            gcongr; exact one_add_pow_le _ hξ0 n
    calc SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ 2 ^ n * (1 + ‖L‖) ^ n * S := hb
      _ ≤ 2 ^ n * ((1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n))) * S := by gcongr
      _ = 2 ^ n * ((1 + ‖A‖) ^ n * 2 ^ n) * S * (1 + ‖ξ‖ ^ n) := by ring

end GlobalTheory.CharFamily
