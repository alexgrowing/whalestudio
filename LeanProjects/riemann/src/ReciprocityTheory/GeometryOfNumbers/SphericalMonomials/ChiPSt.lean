import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.MonoNormSq

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Finset

theorem monoNormSq_pos {D : ℕ} (a : Fin (D + 1) → ℕ) : 0 < monoNormSq a := by
  unfold monoNormSq
  apply div_pos
  · apply mul_pos
    · exact_mod_cast (Finset.prod_pos fun i _ => Nat.factorial_pos (a i))
    · exact_mod_cast Nat.factorial_pos D
  · exact_mod_cast Nat.factorial_pos _

theorem chiPAux_prod_fact_mul_fact_le {D : ℕ} (a : Fin (D + 1) → ℕ) :
    (∏ i, (a i).factorial) * D.factorial ≤ ((∑ i, a i) + D).factorial := by
  have h1 : (∏ i, (a i).factorial) ∣ (∑ i, a i).factorial := by
    first
      | exact Nat.prod_factorial_dvd_factorial_sum _ _
      | exact Nat.prod_factorial_dvd_factorial_sum
  have h2 : (∑ i, a i).factorial * D.factorial ∣ ((∑ i, a i) + D).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add _ _
  exact Nat.le_of_dvd (Nat.factorial_pos _) (dvd_trans (mul_dvd_mul_right h1 _) h2)

theorem monoNormSq_le_one {D : ℕ} (a : Fin (D + 1) → ℕ) : monoNormSq a ≤ 1 := by
  unfold monoNormSq
  have hF : (0 : ℝ) < (((∑ i, a i) + D).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hle : ((∏ i, (a i).factorial : ℕ) : ℝ) * (D.factorial : ℝ) ≤ (((∑ i, a i) + D).factorial : ℝ) := by
    exact_mod_cast chiPAux_prod_fact_mul_fact_le a
  first
    | exact (div_le_one hF).mpr hle
    | exact (div_le_one₀ hF).mpr hle
    | exact div_le_one_of_le₀ hle hF.le

theorem chiPAux_multinomial_univ_le {D : ℕ} (a : Fin (D + 1) → ℕ) :
    Nat.multinomial Finset.univ a ≤ (D + 1) ^ (∑ i, a i) := by
  have key := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin (D + 1))) (fun _ => (1 : ℕ)) (∑ i, a i)
  simp only [one_pow, Finset.prod_const_one, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at key
  rw [key]
  apply Finset.single_le_sum (f := fun k => Nat.multinomial Finset.univ k) (fun _ _ => Nat.zero_le _)
  rw [Finset.mem_piAntidiag]
  exact ⟨rfl, fun i _ => Finset.mem_univ i⟩

private theorem factorial_add_le_mul_pow (n k : ℕ) : (n + k).factorial ≤ n.factorial * (n + k) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, Nat.factorial_succ, pow_succ]
    calc (n + k + 1) * (n + k).factorial ≤ (n + k + 1) * (n.factorial * (n + k) ^ k) :=
          Nat.mul_le_mul (le_refl _) ih
      _ ≤ (n + k + 1) * (n.factorial * (n + k + 1) ^ k) :=
          Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left (Nat.le_succ _) _))
      _ = n.factorial * ((n + k + 1) ^ k * (n + k + 1)) := by ring

theorem factorial_sum_add_le {D : ℕ} (a : Fin (D + 1) → ℕ) :
    ((∑ i, a i) + D).factorial ≤ (D + 1) ^ (∑ i, a i) * ((∑ i, a i) + D) ^ D * ∏ i, (a i).factorial := by
  have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin (D + 1))) a
  have hm := chiPAux_multinomial_univ_le a
  have h1 : (∑ i, a i).factorial ≤ (D + 1) ^ (∑ i, a i) * ∏ i, (a i).factorial := by
    calc (∑ i, a i).factorial = (∏ i, (a i).factorial) * Nat.multinomial Finset.univ a := hspec.symm
      _ ≤ (∏ i, (a i).factorial) * (D + 1) ^ (∑ i, a i) := Nat.mul_le_mul (le_refl _) hm
      _ = (D + 1) ^ (∑ i, a i) * ∏ i, (a i).factorial := mul_comm _ _
  calc ((∑ i, a i) + D).factorial ≤ (∑ i, a i).factorial * ((∑ i, a i) + D) ^ D := factorial_add_le_mul_pow _ _
    _ ≤ ((D + 1) ^ (∑ i, a i) * ∏ i, (a i).factorial) * ((∑ i, a i) + D) ^ D :=
        Nat.mul_le_mul h1 (le_refl _)
    _ = (D + 1) ^ (∑ i, a i) * ((∑ i, a i) + D) ^ D * ∏ i, (a i).factorial := by ring

private theorem inv_le_mul_div_of_le_mul {Q A E F : ℝ} (hF : 0 < F) (hA : 0 < A) (hE : 1 ≤ E) (hQ : 0 ≤ Q)
    (h : F ≤ Q * A) : Q⁻¹ ≤ A * E / F := by
  rcases hQ.eq_or_lt with h0 | h0
  · rw [← h0, inv_zero]
    exact div_nonneg (mul_nonneg hA.le (by linarith)) hF.le
  · have key : Q⁻¹ * F ≤ A * E := by
      calc Q⁻¹ * F ≤ Q⁻¹ * (Q * A) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hQ)
        _ = A := by rw [← mul_assoc, inv_mul_cancel₀ h0.ne', one_mul]
        _ ≤ A * E := le_mul_of_one_le_right hA.le hE
    first
      | exact (le_div_iff₀ hF).mpr key
      | exact (le_div_iff hF).mpr key

theorem le_monoNormSq {D : ℕ} (a : Fin (D + 1) → ℕ) :
    (((D + 1 : ℝ) ^ (∑ i, a i)) * ((∑ i, a i : ℕ) + D : ℝ) ^ D)⁻¹ ≤ monoNormSq a := by
  unfold monoNormSq
  apply inv_le_mul_div_of_le_mul (by exact_mod_cast Nat.factorial_pos _)
    (by exact_mod_cast (Finset.prod_pos fun i _ => Nat.factorial_pos (a i)))
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero D)) (by positivity)
  exact_mod_cast factorial_sum_add_le a

theorem chiPAux_sum_update_zero {D : ℕ} (a : Fin (D + 1) → ℕ) (v : ℕ) :
    ∑ i, Function.update a 0 v i = v + ∑ i : Fin D, a i.succ := by
  rw [Fin.sum_univ_succ]
  simp [Function.update_apply, Fin.succ_ne_zero]

theorem monoNormSq_succ {D : ℕ} (a : Fin (D + 1) → ℕ) :
    monoNormSq (Function.update a 0 (a 0 + 1)) =
      monoNormSq a * ((a 0 + 1 : ℝ) / ((∑ i, a i : ℕ) + D + 1 : ℝ)) := by
  have e0 : Function.update a 0 (a 0 + 1) 0 = a 0 + 1 := by simp
  have es : ∀ i : Fin D, Function.update a 0 (a 0 + 1) i.succ = a i.succ := fun i => by
    simp [Function.update_apply, Fin.succ_ne_zero]
  have hs : ∑ i, Function.update a 0 (a 0 + 1) i = (∑ i, a i) + 1 := by
    rw [chiPAux_sum_update_zero, Fin.sum_univ_succ a]
    ring
  have hp : (∏ i, (Function.update a 0 (a 0 + 1) i).factorial) = (a 0 + 1) * ∏ i, (a i).factorial := by
    simp only [Fin.prod_univ_succ, e0, es, Nat.factorial_succ]
    ring
  have hf : ((∑ i, a i) + 1 + D).factorial = ((∑ i, a i) + D + 1) * ((∑ i, a i) + D).factorial := by
    rw [show (∑ i, a i) + 1 + D = (∑ i, a i) + D + 1 by ring]
    exact Nat.factorial_succ _
  unfold monoNormSq
  rw [hs, hp, hf]
  push_cast
  have hF : (((∑ i, a i) + D).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hg : (∑ i, (a i : ℝ)) + D + 1 ≠ 0 := by positivity
  first
    | (rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero hg hF) (mul_ne_zero hF hg)]; ring)
    | (field_simp; ring)

theorem chiP_nonneg (D n : ℕ) : 0 ≤ chiP D n := by
  unfold chiP
  have h : ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, Real.log (monoNormSq a) ≤ 0 :=
    Finset.sum_nonpos fun a _ => Real.log_nonpos (monoNormSq_pos a).le (monoNormSq_le_one a)
  linarith

theorem chiPAux_card_adt_le (k m : ℕ) : (Finset.Nat.antidiagonalTuple (k + 1) m).card ≤ (m + 1) ^ k := by
  calc (Finset.Nat.antidiagonalTuple (k + 1) m).card
      ≤ (Fintype.piFinset fun _ : Fin k => Finset.range (m + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun b i => b i.succ)
        · intro b hb
          have hb' := Finset.Nat.mem_antidiagonalTuple.mp hb
          simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
          intro i
          have : b i.succ ≤ ∑ j, b j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ _)
          omega
        · intro b hb c hc hbc
          have hb' := Finset.Nat.mem_antidiagonalTuple.mp hb
          have hc' := Finset.Nat.mem_antidiagonalTuple.mp hc
          have hs : ∀ i : Fin k, b i.succ = c i.succ := fun i => congrFun hbc i
          rw [Fin.sum_univ_succ] at hb' hc'
          have hsum : ∑ i : Fin k, b i.succ = ∑ i : Fin k, c i.succ :=
            Finset.sum_congr rfl (fun i _ => hs i)
          funext j
          refine Fin.cases ?_ (fun i => hs i) j
          omega
    _ = (m + 1) ^ k := by simp

theorem chiPAux_card_filter_zero_le (D n : ℕ) :
    ((Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0)).card ≤
      (Finset.Nat.antidiagonalTuple D (n + 1)).card := by
  apply Finset.card_le_card_of_injOn (fun b i => b i.succ)
  · intro b hb
    have h0 : b 0 = 0 := (Finset.mem_filter.mp hb).2
    have h1 := Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hb).1
    rw [Fin.sum_univ_succ, h0, zero_add] at h1
    exact Finset.Nat.mem_antidiagonalTuple.mpr h1
  · intro b hb c hc hbc
    have hb0 : b 0 = 0 := (Finset.mem_filter.mp hb).2
    have hc0 : c 0 = 0 := (Finset.mem_filter.mp hc).2
    funext j
    refine Fin.cases ?_ (fun i => congrFun hbc i) j
    rw [hb0, hc0]

theorem chiPAux_filter_zero_eq_empty (n : ℕ) :
    (Finset.Nat.antidiagonalTuple (0 + 1) (n + 1)).filter (fun b => b 0 = 0) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro b hb h0
  have h1 := Finset.Nat.mem_antidiagonalTuple.mp hb
  simp [Fin.sum_univ_succ, h0] at h1 <;> omega

theorem chiPAux_sum_split (D n : ℕ) (g : (Fin (D + 1) → ℕ) → ℝ) :
    ∑ b ∈ Finset.Nat.antidiagonalTuple (D + 1) (n + 1), g b =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, g (Function.update a 0 (a 0 + 1)) +
      ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0), g b := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Nat.antidiagonalTuple (D + 1) (n + 1))
    (fun b : Fin (D + 1) → ℕ => b 0 = 0)]
  have key : ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, g (Function.update a 0 (a 0 + 1)) =
      ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => ¬ b 0 = 0), g b := by
    apply Finset.sum_nbij' (fun a => Function.update a 0 (a 0 + 1)) (fun b => Function.update b 0 (b 0 - 1))
    · intro a ha
      have ha' := Finset.Nat.mem_antidiagonalTuple.mp ha
      rw [Fin.sum_univ_succ] at ha'
      refine Finset.mem_filter.mpr ⟨Finset.Nat.mem_antidiagonalTuple.mpr ?_, ?_⟩
      · rw [chiPAux_sum_update_zero]
        omega
      · simp [Function.update_apply]
    · intro b hb
      have h1 := Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hb).1
      have h2 : b 0 ≠ 0 := (Finset.mem_filter.mp hb).2
      rw [Fin.sum_univ_succ] at h1
      apply Finset.Nat.mem_antidiagonalTuple.mpr
      rw [chiPAux_sum_update_zero]
      omega
    · intro a _
      funext i
      by_cases hi : i = 0
      · subst hi
        simp [Function.update_apply]
      · simp [Function.update_apply, hi]
    · intro b hb
      have h2 : b 0 ≠ 0 := (Finset.mem_filter.mp hb).2
      funext i
      by_cases hi : i = 0
      · subst hi
        simp [Function.update_apply] <;> omega
      · simp [Function.update_apply, hi]
    · intro a _
      rfl
  linarith [key]

theorem chiP_succ_sub_eq (D n : ℕ) :
    chiP D (n + 1) - chiP D n = (1 / 2) *
      (∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) +
       ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
          -Real.log (monoNormSq b)) := by
  unfold chiP
  rw [chiPAux_sum_split D n (fun b => Real.log (monoNormSq b))]
  have hstep : ∀ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n,
      Real.log (monoNormSq (Function.update a 0 (a 0 + 1))) =
        Real.log (monoNormSq a) + Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) := by
    intro a ha
    have ha' := Finset.Nat.mem_antidiagonalTuple.mp ha
    rw [monoNormSq_succ, ha', Real.log_mul (monoNormSq_pos a).ne' (by positivity)]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  simp only [Finset.sum_neg_distrib]
  ring

theorem chiPAux_neg_log_step_mem (D n : ℕ) (a : Fin (D + 1) → ℕ) (ha : a ∈ Finset.Nat.antidiagonalTuple (D + 1) n) :
    0 ≤ -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) ∧
      -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) ≤ Real.log ((n : ℝ) + D + 1) := by
  have ha' := Finset.Nat.mem_antidiagonalTuple.mp ha
  have h0 : a 0 ≤ n := by
    rw [← ha']
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (a i)) (Finset.mem_univ 0)
  have h0' : (a 0 : ℝ) ≤ n := by exact_mod_cast h0
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have ha0 : (0 : ℝ) ≤ a 0 := Nat.cast_nonneg _
  have hden : (0 : ℝ) < (n : ℝ) + D + 1 := by positivity
  have hpos : (0 : ℝ) < (a 0 + 1 : ℝ) / ((n : ℝ) + D + 1) := by positivity
  have hle1 : (a 0 + 1 : ℝ) / ((n : ℝ) + D + 1) ≤ 1 := by
    have hnum : (a 0 + 1 : ℝ) ≤ (n : ℝ) + D + 1 := by linarith
    first
      | exact (div_le_one hden).mpr hnum
      | exact (div_le_one₀ hden).mpr hnum
      | exact div_le_one_of_le₀ hnum hden.le
  constructor
  · have := Real.log_nonpos hpos.le hle1
    linarith
  · rw [Real.log_div (by positivity) (by positivity)]
    have : 0 ≤ Real.log ((a 0 : ℝ) + 1) := Real.log_nonneg (by linarith)
    linarith

theorem chiPAux_neg_log_monoNormSq_le {D : ℕ} (b : Fin (D + 1) → ℕ) :
    -Real.log (monoNormSq b) ≤
      (∑ i, b i : ℕ) * Real.log (D + 1) + D * Real.log ((∑ i, b i : ℕ) + D) := by
  have hQ := le_monoNormSq b
  have hA : (0 : ℝ) < (D + 1 : ℝ) ^ (∑ i, b i) := by positivity
  have hB : (0 : ℝ) < ((∑ i, b i : ℕ) + D : ℝ) ^ D := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      simp
    · apply pow_pos
      have h1 : (0 : ℝ) < D := by exact_mod_cast hD
      have h2 : (0 : ℝ) ≤ ((∑ i, b i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  have hQpos : 0 < (D + 1 : ℝ) ^ (∑ i, b i) * ((∑ i, b i : ℕ) + D : ℝ) ^ D := mul_pos hA hB
  have hlog : Real.log (((D + 1 : ℝ) ^ (∑ i, b i)) * ((∑ i, b i : ℕ) + D : ℝ) ^ D)⁻¹ ≤
      Real.log (monoNormSq b) := by
    first
      | exact Real.log_le_log (inv_pos.mpr hQpos) hQ
      | exact (Real.log_le_log_iff (inv_pos.mpr hQpos) (monoNormSq_pos b)).mpr hQ
  rw [Real.log_inv, Real.log_mul hA.ne' hB.ne', Real.log_pow, Real.log_pow] at hlog
  linarith

theorem chiPAux_neg_log_monoNormSq_nonneg {D : ℕ} (b : Fin (D + 1) → ℕ) : 0 ≤ -Real.log (monoNormSq b) := by
  have := Real.log_nonpos (monoNormSq_pos b).le (monoNormSq_le_one b)
  linarith

theorem chiP_succ_sub_nonneg (D n : ℕ) : 0 ≤ chiP D (n + 1) - chiP D n := by
  rw [chiP_succ_sub_eq]
  have h1 : 0 ≤ ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n,
      -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) :=
    Finset.sum_nonneg fun a ha => (chiPAux_neg_log_step_mem D n a ha).1
  have h2 : 0 ≤ ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
      -Real.log (monoNormSq b) :=
    Finset.sum_nonneg fun b _ => chiPAux_neg_log_monoNormSq_nonneg b
  linarith

theorem exists_chiP_le (D : ℕ) : ∃ C : ℝ, ∀ n : ℕ, chiP D n ≤ C * (n : ℝ) ^ (D + 1) := by
  obtain ⟨K, hKe⟩ : ∃ K : ℝ, K = Real.log ((D : ℝ) + 1) + D * (1 + D) := ⟨_, rfl⟩
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hK : 0 ≤ K := by
    have h1 : 0 ≤ Real.log ((D : ℝ) + 1) := Real.log_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ D * (1 + D) := by positivity
    rw [hKe]
    linarith
  refine ⟨2 ^ D * K, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hz : chiP D 0 = 0 := by
      unfold chiP
      have hsum0 : ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) 0, Real.log (monoNormSq a) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        have hs := Finset.Nat.mem_antidiagonalTuple.mp ha
        have hz : ∀ i, a i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hs) i (Finset.mem_univ i)
        have hm : monoNormSq a = 1 := by
          unfold monoNormSq
          rw [hs]
          simp only [hz, Nat.factorial_zero, Finset.prod_const_one, Nat.cast_one, one_mul, zero_add]
          exact div_self (by exact_mod_cast Nat.factorial_ne_zero D)
        rw [hm, Real.log_one]
      rw [hsum0]
      ring
    rw [hz]
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have hterm : ∀ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, -Real.log (monoNormSq a) ≤ n * K := by
      intro a ha
      have hs := Finset.Nat.mem_antidiagonalTuple.mp ha
      have h1 := chiPAux_neg_log_monoNormSq_le a
      rw [hs] at h1
      have hlog : Real.log ((n : ℝ) + D) ≤ (n : ℝ) + D := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) + D by linarith)
        linarith
      have h2 : (D : ℝ) * Real.log ((n : ℝ) + D) ≤ D * ((n : ℝ) + D) := mul_le_mul_of_nonneg_left hlog hD0
      have h3 : (D : ℝ) * ((n : ℝ) + D) ≤ n * (D * (1 + D)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg (D : ℝ))]
      rw [hKe]
      linarith
    have hsum : chiP D n ≤ (1 / 2) * (((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) * (n * K)) := by
      unfold chiP
      have h := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_neg_distrib] at h
      linarith
    have hcard : ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) ≤ 2 ^ D * (n : ℝ) ^ D := by
      have h1 : ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) ≤ ((n : ℝ) + 1) ^ D := by
        exact_mod_cast chiPAux_card_adt_le D n
      have h2 : ((n : ℝ) + 1) ^ D ≤ (2 * (n : ℝ)) ^ D := by
        gcongr
        linarith
      rw [mul_pow] at h2
      linarith
    have hnK : 0 ≤ (n : ℝ) * K := mul_nonneg hn0 hK
    have hc0 : (0 : ℝ) ≤ ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) := Nat.cast_nonneg _
    calc chiP D n ≤ (1 / 2) * (((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) * (n * K)) := hsum
      _ ≤ ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) * (n * K) := by
          linarith [mul_nonneg hc0 hnK]
      _ ≤ (2 ^ D * (n : ℝ) ^ D) * (n * K) := mul_le_mul_of_nonneg_right hcard hnK
      _ = 2 ^ D * K * (n : ℝ) ^ (D + 1) := by ring

theorem chiPAux_sum_filter_zero_le (D n : ℕ) (hn : 1 ≤ n) (P : ℝ) (hP : 0 ≤ P)
    (hb : ∀ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
      -Real.log (monoNormSq b) ≤ (2 + (D : ℝ)) * n * P) :
    ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
      -Real.log (monoNormSq b) ≤ 3 ^ D * (2 + (D : ℝ)) * P * (n : ℝ) ^ D := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hcard : ((((Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0)).card : ℕ) : ℝ)
      * n ≤ 3 ^ D * (n : ℝ) ^ D := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      rw [chiPAux_filter_zero_eq_empty]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, D = k + 1 := ⟨D - 1, by omega⟩
      have h1 : ((((Finset.Nat.antidiagonalTuple (k + 1 + 1) (n + 1)).filter (fun b => b 0 = 0)).card : ℕ) : ℝ)
          ≤ ((n : ℝ) + 1 + 1) ^ k := by
        have := (chiPAux_card_filter_zero_le (k + 1) n).trans (chiPAux_card_adt_le k (n + 1))
        exact_mod_cast this
      have h2 : ((n : ℝ) + 1 + 1) ^ k ≤ (3 * (n : ℝ)) ^ k := by
        gcongr
        linarith
      have h3 : (0 : ℝ) ≤ 3 ^ k * (n : ℝ) ^ (k + 1) := by positivity
      calc ((((Finset.Nat.antidiagonalTuple (k + 1 + 1) (n + 1)).filter (fun b => b 0 = 0)).card : ℕ) : ℝ)
            * n ≤ (3 * (n : ℝ)) ^ k * n := mul_le_mul_of_nonneg_right (h1.trans h2) hn0
        _ = 3 ^ k * (n : ℝ) ^ (k + 1) := by ring
        _ ≤ 3 ^ (k + 1) * (n : ℝ) ^ (k + 1) := by
          have e : (3 : ℝ) ^ (k + 1) = 3 * 3 ^ k := by ring
          rw [e]
          linarith
  have hsum := Finset.sum_le_sum hb
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hP0 : 0 ≤ (2 + (D : ℝ)) * P := mul_nonneg (by linarith) hP
  refine hsum.trans ?_
  calc ((((Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0)).card : ℕ) : ℝ)
        * ((2 + (D : ℝ)) * n * P)
      = (((((Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0)).card : ℕ) : ℝ)
          * n) * ((2 + (D : ℝ)) * P) := by ring
    _ ≤ (3 ^ D * (n : ℝ) ^ D) * ((2 + (D : ℝ)) * P) := mul_le_mul_of_nonneg_right hcard hP0
    _ = 3 ^ D * (2 + (D : ℝ)) * P * (n : ℝ) ^ D := by ring

private theorem log_add_add_one_le_log_add_log (n D : ℕ) :
    Real.log ((n : ℝ) + D + 1) ≤ Real.log ((n : ℝ) + 1) + Real.log ((D : ℝ) + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  rw [← Real.log_mul (by positivity) (by positivity)]
  have hle : (n : ℝ) + D + 1 ≤ ((n : ℝ) + 1) * ((D : ℝ) + 1) := by nlinarith [mul_nonneg hn hD]
  first
    | exact Real.log_le_log (by positivity) hle
    | exact (Real.log_le_log_iff (by positivity) (by positivity)).mpr hle

theorem exists_chiP_succ_sub_le (D : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = Real.log ((D : ℝ) + 1) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c₀ := by
    rw [hc₀]
    exact Real.log_nonneg (by linarith)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = c₀ / Real.log 2 := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact div_nonneg hc0 hl2.le
  have hcL : ∀ t : ℝ, Real.log 2 ≤ t → c₀ ≤ L * t := by
    intro t ht
    have e : c₀ = L * Real.log 2 := by
      rw [hL]
      first
        | exact (div_mul_cancel₀ c₀ hl2.ne').symm
        | field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left ht hL0
  refine ⟨(1 / 2) * (2 ^ D + 3 ^ D * (2 + (D : ℝ))) * (1 + L), fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ t : ℝ, t = Real.log ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hℓ2 : Real.log 2 ≤ ℓ := by
    rw [hℓ]
    first
      | exact Real.log_le_log (by norm_num) (by linarith)
      | exact (Real.log_le_log_iff (by norm_num) (by linarith)).mpr (by linarith)
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hc : c₀ ≤ L * ℓ := hcL ℓ hℓ2
  have hlogND : Real.log ((n : ℝ) + D + 1) ≤ ℓ + c₀ := by
    rw [hℓ, hc₀]
    exact log_add_add_one_le_log_add_log n D
  have hX : 0 ≤ (1 + L) * ℓ := mul_nonneg (by linarith) hℓ0
  have hS1 : ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1))
      ≤ 2 ^ D * (n : ℝ) ^ D * ((1 + L) * ℓ) := by
    have h1 : ∀ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n,
        -Real.log ((a 0 + 1 : ℝ) / ((n : ℝ) + D + 1)) ≤ (1 + L) * ℓ := by
      intro a ha
      have := (chiPAux_neg_log_step_mem D n a ha).2
      linarith
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have hcard : ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) ≤ 2 ^ D * (n : ℝ) ^ D := by
      have h3 : ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) ≤ ((n : ℝ) + 1) ^ D := by
        exact_mod_cast chiPAux_card_adt_le D n
      have h4 : ((n : ℝ) + 1) ^ D ≤ (2 * (n : ℝ)) ^ D := by
        gcongr
        linarith
      rw [mul_pow] at h4
      linarith
    exact h2.trans (mul_le_mul_of_nonneg_right hcard hX)
  have hS2 : ∑ b ∈ (Finset.Nat.antidiagonalTuple (D + 1) (n + 1)).filter (fun b => b 0 = 0),
      -Real.log (monoNormSq b) ≤ 3 ^ D * (2 + (D : ℝ)) * ((1 + L) * ℓ) * (n : ℝ) ^ D := by
    apply chiPAux_sum_filter_zero_le D n hn ((1 + L) * ℓ) hX
    intro b hb
    have hs := Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp hb).1
    have h1 := chiPAux_neg_log_monoNormSq_le b
    rw [hs] at h1
    push_cast at h1
    have e : (n : ℝ) + 1 + D = (n : ℝ) + D + 1 := by ring
    rw [e, ← hc₀] at h1
    have h2 : (D : ℝ) * Real.log ((n : ℝ) + D + 1) ≤ D * (ℓ + c₀) := mul_le_mul_of_nonneg_left hlogND hD0
    have h3 : ((n : ℝ) + 1) * c₀ ≤ ((n : ℝ) + 1) * (L * ℓ) := mul_le_mul_of_nonneg_left hc (by linarith)
    have h4 : (D : ℝ) * c₀ ≤ D * (L * ℓ) := mul_le_mul_of_nonneg_left hc hD0
    have hLl : 0 ≤ L * ℓ := mul_nonneg hL0 hℓ0
    have h5 : 0 ≤ ((n : ℝ) - 1) * (L * ℓ) := mul_nonneg (by linarith) hLl
    have h6 : 0 ≤ (D : ℝ) * ℓ * ((n : ℝ) - 1) := mul_nonneg (mul_nonneg hD0 hℓ0) (by linarith)
    have h7 : 0 ≤ (D : ℝ) * (L * ℓ) * ((n : ℝ) - 1) := mul_nonneg (mul_nonneg hD0 hLl) (by linarith)
    have h8 : 0 ≤ (n : ℝ) * ℓ := mul_nonneg hn0 hℓ0
    linarith
  rw [chiP_succ_sub_eq, ← hℓ]
  calc _ ≤ (1 / 2) * (2 ^ D * (n : ℝ) ^ D * ((1 + L) * ℓ)
          + 3 ^ D * (2 + (D : ℝ)) * ((1 + L) * ℓ) * (n : ℝ) ^ D) := by linarith
    _ = (1 / 2) * (2 ^ D + 3 ^ D * (2 + (D : ℝ))) * (1 + L) * (n : ℝ) ^ D * ℓ := by ring

end ReciprocityTheory.GeometryOfNumbersTheory
