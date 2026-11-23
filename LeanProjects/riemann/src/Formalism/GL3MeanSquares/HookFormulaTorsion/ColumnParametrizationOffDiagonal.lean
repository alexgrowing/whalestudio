import Mathlib
import Formalism.GL3MeanSquares.IntegralMultipleNormLowerBound

namespace Formalism.HermitianLattices.ExplicitEstimates

open Finset
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (hookF)

private theorem g4w9_prod_gt (N : ℕ) (i : Fin (N + 1)) (g : ℕ → ℝ) :
    ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j), g ((j : ℕ) - i)
      = ∏ t ∈ range (N - i), g (t + 1) := by
  have hi := i.isLt
  refine Finset.prod_nbij' (fun j => (j : ℕ) - (i : ℕ) - 1)
    (fun t => if h : t + 1 + (i : ℕ) < N + 1 then (⟨t + 1 + (i : ℕ), h⟩ : Fin (N + 1)) else 0)
    ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj
    have hj2 := j.isLt
    simp only [Finset.mem_range]
    omega
  · intro t ht
    simp only [Finset.mem_range] at ht
    have h : t + 1 + (i : ℕ) < N + 1 := by omega
    simp only [dif_pos h, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val,
      Fin.val_mk]
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj
    have hj2 := j.isLt
    have h : (j : ℕ) - (i : ℕ) - 1 + 1 + (i : ℕ) < N + 1 := by omega
    simp only [dif_pos h, Fin.ext_iff, Fin.val_mk]
    omega
  · intro t ht
    simp only [Finset.mem_range] at ht
    have h : t + 1 + (i : ℕ) < N + 1 := by omega
    simp only [dif_pos h, Fin.val_mk]
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_iff_val_lt_val] at hj
    show g ((j : ℕ) - (i : ℕ)) = g ((j : ℕ) - (i : ℕ) - 1 + 1)
    congr 1
    omega

private theorem g4w9_fact_range (a m : ℕ) :
    ((a + m).factorial : ℝ) = (a.factorial : ℝ) * ∏ t ∈ range m, ((a : ℝ) + ((t + 1 : ℕ) : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a + (m + 1) = (a + m) + 1 := by omega
    rw [e, Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]
    push_cast
    ring

private theorem g4w9_sum_count (N : ℕ) :
    ∑ i : Fin (N + 1), (N - (i : ℕ)) = (N + 1) * N / 2 := by
  refine (Fin.sum_univ_eq_sum_range (fun i => N - i) (N + 1)).trans ?_
  have h1 : ∑ i ∈ range (N + 1), (N - i) = ∑ j ∈ range (N + 1), (N + 1 - 1 - j) :=
    Finset.sum_congr rfl (fun i _ => by omega)
  have h2 : ∑ j ∈ range (N + 1), (N + 1 - 1 - j) = ∑ j ∈ range (N + 1), j :=
    Finset.sum_range_reflect (fun i => i) (N + 1)
  show ∑ i ∈ range (N + 1), (N - i) = _
  rw [h1, h2, Finset.sum_range_id]
  simp

theorem lemma_c_explicit_bounds : LemC_bounds := by
  intro N nu hnu
  unfold hookF
  have hd : ∀ i j : Fin (N + 1), i < j →
      (1:ℝ) ≤ ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) ∧
      ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ)
        ≤ (nu i : ℝ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) := by
    intro i j hij
    have h1 := hnu (le_of_lt hij)
    have h2 : (i : ℕ) < j := Fin.lt_iff_val_lt_val.mp hij
    constructor
    · have h3 : (1:ℤ) ≤ (nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by omega
      exact_mod_cast h3
    · have h3 : (nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)
          ≤ (nu i : ℤ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℤ) := by omega
      exact_mod_cast h3
  have hper : ∀ i : Fin (N + 1),
      ((nu i).factorial : ℝ) ≤ ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) /
          ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) ∧
      ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) /
          ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ)
        ≤ ((nu i).factorial : ℝ) * ((nu 0 : ℝ) + N + 1) ^ (N - (i : ℕ)) := by
    intro i
    have hi := i.isLt
    have e1 : nu i + (N + 1) - 1 - (i : ℕ) = nu i + (N - (i : ℕ)) := by omega
    have hF : ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ)
        = ((nu i).factorial : ℝ) * ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ)) := by
      rw [e1]
      exact g4w9_fact_range (nu i) (N - (i : ℕ))
    have hAle : ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ)
        ≤ ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ)) := by
      calc _ ≤ ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
              ((nu i : ℝ) + (((j : ℕ) - (i : ℕ) : ℕ) : ℝ)) :=
            Finset.prod_le_prod
              (fun j hj => le_trans zero_le_one (hd i j (Finset.mem_filter.mp hj).2).1)
              (fun j hj => (hd i j (Finset.mem_filter.mp hj).2).2)
        _ = _ := g4w9_prod_gt N i (fun x => (nu i : ℝ) + (x : ℝ))
    have hA1 : (1:ℝ) ≤ ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j),
            ((((nu i : ℤ) - (nu j : ℤ) + ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℤ) : ℝ) := by
      calc (1:ℝ) = ∏ j ∈ univ.filter (fun j : Fin (N + 1) => i < j), (1:ℝ) :=
            Finset.prod_const_one.symm
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
              (fun j hj => (hd i j (Finset.mem_filter.mp hj).2).1)
    have hPle : ∏ t ∈ range (N - (i : ℕ)), ((nu i : ℝ) + ((t + 1 : ℕ) : ℝ))
        ≤ ((nu 0 : ℝ) + N + 1) ^ (N - (i : ℕ)) := by
      have h0i : nu i ≤ nu 0 := hnu (by simp [Fin.le_iff_val_le_val])
      calc _ ≤ ∏ t ∈ range (N - (i : ℕ)), ((nu 0 : ℝ) + N + 1) :=
            Finset.prod_le_prod (fun t _ => by positivity)
              (fun t ht => by
                have ht' := Finset.mem_range.mp ht
                have h5 : nu i + (t + 1) ≤ nu 0 + N + 1 := by omega
                exact_mod_cast h5)
        _ = _ := by rw [Finset.prod_const, Finset.card_range]
    have hApos := lt_of_lt_of_le zero_lt_one hA1
    have hfac : (0:ℝ) ≤ ((nu i).factorial : ℝ) := by positivity
    constructor
    · rw [le_div_iff₀ hApos, hF]
      exact mul_le_mul_of_nonneg_left hAle hfac
    · calc _ ≤ ((nu i + (N + 1) - 1 - (i : ℕ)).factorial : ℝ) := div_le_self (by positivity) hA1
        _ = _ := hF
        _ ≤ _ := mul_le_mul_of_nonneg_left hPle hfac
  rw [← Finset.prod_div_distrib]
  constructor
  · exact Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => (hper i).1)
  · calc _ ≤ ∏ i : Fin (N + 1), (((nu i).factorial : ℝ) * ((nu 0 : ℝ) + N + 1) ^ (N - (i : ℕ))) :=
          Finset.prod_le_prod (fun i _ => le_trans (by positivity) (hper i).1) (fun i _ => (hper i).2)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, g4w9_sum_count N]

theorem mean_log_explicit : MeanLogExplicit := by
  intro d k h v hd hk hv hpos hcol
  have hdpos : (0:ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hXpos : ∀ τ, 0 < ∑ c, h τ c := by
    intro τ
    exact Finset.sum_pos (fun c _ => hpos τ c) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hcol' : ∀ c, ∑ τ, h τ c ≤ d * ((k:ℝ) ^ 2 * (2 * v) ^ 2) := by
    intro c
    have h1 := hcol c
    rw [div_le_iff₀ hdpos] at h1
    linarith
  have hT : ∑ τ, ∑ c, h τ c ≤ d * ((k:ℝ) ^ 3 * (2 * v) ^ 2) := by
    rw [Finset.sum_comm]
    have h1 : ∑ c : Fin k, ∑ τ : Fin d, h τ c ≤ ∑ c : Fin k, ((d:ℝ) * ((k:ℝ) ^ 2 * (2 * v) ^ 2)) :=
      Finset.sum_le_sum (fun c _ => hcol' c)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    calc _ ≤ _ := h1
      _ = _ := by ring
  have hTpos : 0 < ∑ τ, ∑ c, h τ c :=
    Finset.sum_pos (fun τ _ => hXpos τ) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (∑ τ, ∑ c, h τ c) / d := ⟨_, rfl⟩
  have hMpos : 0 < M := by rw [hM]; exact div_pos hTpos hdpos
  have hstep : ∀ τ, Real.log (∑ c, h τ c) ≤ Real.log M + (∑ c, h τ c) / M - 1 := by
    intro τ
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hXpos τ) hMpos)
    rw [Real.log_div (hXpos τ).ne' hMpos.ne'] at h1
    linarith
  have hsum1 : ∑ τ, Real.log (∑ c, h τ c) ≤ ∑ τ : Fin d, (Real.log M + (∑ c, h τ c) / M - 1) :=
    Finset.sum_le_sum (fun τ _ => hstep τ)
  have hsum2 : ∑ τ : Fin d, (Real.log M + (∑ c, h τ c) / M - 1)
      = d * Real.log M + (∑ τ, ∑ c, h τ c) / M - d := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hsum3 : (∑ τ, ∑ c, h τ c) / M = d := by
    have h1 := hTpos.ne'
    have h2 := hdpos.ne'
    rw [hM]
    field_simp
  have hMle : M ≤ (k:ℝ) ^ 3 * (2 * v) ^ 2 := by
    rw [hM, div_le_iff₀ hdpos]
    linarith
  have hlog := Real.log_le_log hMpos hMle
  have hfin := mul_le_mul_of_nonneg_left hlog hdpos.le
  rw [div_le_iff₀ hdpos]
  linarith

theorem explicit_zeta_bound_rank_five : AntitoneWeightLogBoundExplicit := by
  intro κ lam v logT logB logc muB mu hv hanti hB hc hmuB hmu
  have hW0 : 0 ≤ wt (plus lam) := by
    simp only [wt, plus]
    exact Finset.sum_nonneg (fun i _ => by have := hanti (Fin.le_last i); linarith)
  have hW : (0:ℝ) ≤ (wt (plus lam) : ℝ) := by exact_mod_cast hW0
  have hk : (0:ℝ) < (κ:ℝ) + 1 := by positivity
  have hv0 : (0:ℝ) < v := by linarith
  have hkey : Real.log ((κ:ℝ) + 1) + Real.log (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2)
      ≤ 4 * Real.log (((κ:ℝ) + 1) * v) := by
    have hpos2 : (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2) ≠ 0 := by positivity
    have e4 : 4 * Real.log (((κ:ℝ) + 1) * v) = Real.log ((((κ:ℝ) + 1) * v) ^ 4) := by
      rw [Real.log_pow]
      norm_num
    rw [← Real.log_mul hk.ne' hpos2, e4]
    apply Real.log_le_log (by positivity)
    have hv2 : (4:ℝ) ≤ v ^ 2 := by nlinarith
    have hP : (0:ℝ) ≤ ((κ:ℝ) + 1) ^ 4 * v ^ 2 := by positivity
    have e1 : ((κ:ℝ) + 1) * (4 * ((κ:ℝ) + 1) ^ 3 * v ^ 2) = 4 * (((κ:ℝ) + 1) ^ 4 * v ^ 2) := by ring
    have e2 : (((κ:ℝ) + 1) * v) ^ 4 = (((κ:ℝ) + 1) ^ 4 * v ^ 2) * v ^ 2 := by ring
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_left hv2 hP]
  have h1 := mul_le_mul_of_nonneg_left hB hW
  have h2 := mul_le_mul_of_nonneg_left hkey hW
  linarith

private theorem g4w9_dec (K m s : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta) :
    ∀ d i, i + d < 2 * K → U (i + d) + (d : ℤ) ≤ U i := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hi
    have h1 := ih i (by omega)
    have h2 := L.chain (i + d) (by omega)
    have e : i + (d + 1) = i + d + 1 := by omega
    rw [e]
    push_cast
    linarith [h2.1, h2.2]

private theorem g4w9_dec' (K m s : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta)
    (i j : ℕ) (hij : i ≤ j) (hj : j < 2 * K) : U j + (j : ℤ) ≤ U i + (i : ℤ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have h := g4w9_dec K m s U v b e S eta L d i (by omega)
  push_cast
  linarith

private theorem g4w9_anti (K m s κ : ℕ) (U v b e : ℕ → ℤ) (S eta : ℤ) (L : Layout K m s U v b e S eta)
    (hκ : κ + 1 = 2 * K) : Antitone (colW K U (k := κ + 1)) := by
  intro i j hij
  have hj : (j : ℕ) < 2 * K := by have := j.isLt; omega
  have h := g4w9_dec' K m s U v b e S eta L i j (Fin.le_iff_val_le_val.mp hij) hj
  simp only [colW]
  linarith

theorem column_parametrization_top_entry : ColumnParameterMaximalCondition := by
  intro K m s κ U v b e S eta A bt L hT hκ
  have hK := L.one_le_K
  have hKz : (1:ℤ) ≤ K := by exact_mod_cast hK
  have hκz : (κ:ℤ) + 1 = 2 * K := by exact_mod_cast hκ
  have hcw : ∀ i : Fin (κ + 1), colW K U i = U i - K + ((i : ℕ) : ℤ) + 1 := fun i => rfl
  refine ⟨g4w9_anti K m s κ U v b e S eta L hκ, ?_, ?_, ?_⟩
  · rw [hcw]
    simp only [Fin.val_zero, Nat.cast_zero]
    linarith [hT.1]
  · rw [hcw, Fin.val_last]
    have e0 : 2 * K - 1 = κ := by omega
    have h2 := hT.2
    rw [e0] at h2
    linarith
  · intro i hi0 hil
    have hi := i.isLt
    have h0 : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext (by simpa using h))
    have hl : (i : ℕ) ≠ κ := fun h => hil (Fin.ext (by simpa using h))
    have hA := g4w9_dec' K m s U v b e S eta L 1 i (by omega) (by omega)
    have hB := g4w9_dec' K m s U v b e S eta L i (2 * K - 2) (by omega) (by omega)
    have hc1 := L.cloud_u 1 le_rfl (by omega)
    have hc2 := L.cloud_u (2 * K - 2) (by omega) (by omega)
    have e2 : (((2 * K - 2 : ℕ)) : ℤ) = 2 * (K : ℤ) - 2 := by omega
    rw [hcw]
    push_cast at hA
    constructor <;> linarith [hc1.2, hc2.1]

theorem column_parametrization_off_diagonal : Col_param_off := by
  intro K m s κ U v b e S eta L hO hκ
  obtain ⟨hO1, hO2, hO3, hO4⟩ := hO
  have hK := L.one_le_K
  have hKz : (1:ℤ) ≤ K := by exact_mod_cast hK
  have hκz : (κ:ℤ) + 1 = 2 * K := by exact_mod_cast hκ
  have hκ1 : 1 ≤ κ := by omega
  have hanti := g4w9_anti K m s κ U v b e S eta L hκ
  have hv0 := L.cloud_v 0 (by omega)
  have hvl := L.cloud_v (2 * K - 2) (by omega)
  have eK : 2 * K - 1 = κ := by omega
  rw [eK] at hO3
  have hU : ∀ j : ℕ, 1 ≤ j → j ≤ κ → U j + 1 ≤ S := by
    intro j hj1 hjk
    rcases Nat.lt_or_ge j κ with h | h
    · exact (L.cloud_u j hj1 (by omega)).2
    · have hjκ : j = κ := by omega
      rw [hjκ]
      linarith [hvl.2]
  have hU0 : U 0 + 1 ≤ 3 * S := by linarith [hv0.2]
  have hcw : ∀ i : Fin (κ + 1), colW K U i = U i - K + ((i : ℕ) : ℤ) + 1 := fun i => rfl
  have hlast : colW K U (Fin.last κ) = v (2 * K - 2) + K - 1 := by
    rw [hcw, Fin.val_last, hO3]
    linarith
  have hzero : colW K U (0 : Fin (κ + 1)) = U 0 - K + 1 := by
    rw [hcw]
    simp
  have hlo : ∀ i : Fin (κ + 1), colW K U (Fin.last κ) ≤ colW K U i :=
    fun i => hanti (Fin.le_last i)
  have hhi : ∀ i : Fin (κ + 1), colW K U i ≤ colW K U 0 :=
    fun i => hanti (by simp [Fin.le_iff_val_le_val])
  have hb : ∀ i : Fin (κ + 1), 0 ≤ colW K U i ∧ colW K U i ≤ 3 * S := by
    intro i
    have h1 := hlo i
    have h2 := hhi i
    rw [hlast] at h1
    rw [hzero] at h2
    constructor <;> linarith [hvl.1]
  have hc : ∀ i : Fin (κ + 1), i ≠ 0 → colW K U i - colW K U (Fin.last κ) ≤ S := by
    intro i hi
    have h0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
    have hik : (i : ℕ) ≤ κ := by have := i.isLt; omega
    have hikz : ((i : ℕ) : ℤ) ≤ κ := by exact_mod_cast hik
    have h2 := hU i (by omega) hik
    rw [hcw i, hlast]
    linarith [hvl.1]
  have hpair : ∀ i : Fin (κ + 1), colW K U i + colW K U (Fin.rev i) ≤ 4 * S := by
    intro i
    have hi := i.isLt
    have hjk : (i : ℕ) ≤ κ := by omega
    rw [hcw, hcw, Fin.val_rev]
    have e1 : κ + 1 - ((i : ℕ) + 1) = κ - (i : ℕ) := by omega
    rw [e1]
    have e2 : (((κ - (i : ℕ) : ℕ)) : ℤ) = (κ : ℤ) - ((i : ℕ) : ℤ) := by omega
    have hUk := hU κ hκ1 le_rfl
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · have a1 : U (i : ℕ) = U 0 := by rw [h0]
      have a2 : U (κ - (i : ℕ)) = U κ := by rw [h0, Nat.sub_zero]
      have a3 : ((i : ℕ) : ℤ) = 0 := by omega
      linarith
    · rcases Nat.lt_or_ge (i : ℕ) κ with h1 | h1
      · have u1 := hU i h0 hjk
        have u2 := hU (κ - (i : ℕ)) (by omega) (by omega)
        linarith
      · have hik : (i : ℕ) = κ := by omega
        have a1 : U (i : ℕ) = U κ := by rw [hik]
        have a2 : U (κ - (i : ℕ)) = U 0 := by rw [hik, Nat.sub_self]
        have a3 : ((i : ℕ) : ℤ) = κ := by omega
        linarith
  refine ⟨hanti, hb, hc, ?_, ?_, ?_⟩
  · simp only [wt, plus]
    rw [Fin.sum_univ_succ]
    have h1 : ∑ j : Fin κ, (colW K U j.succ - colW K U (Fin.last κ)) ≤ ∑ j : Fin κ, S :=
      Finset.sum_le_sum (fun j _ => hc j.succ (Fin.succ_ne_zero j))
    have h2 : ∑ j : Fin κ, S = (κ : ℤ) * S := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : colW K U (0 : Fin (κ + 1)) - colW K U (Fin.last κ) ≤ 3 * S := by
      rw [hzero, hlast]
      linarith [hvl.1]
    linarith
  · simp only [wt]
    exact Finset.sum_nonneg (fun i _ => (hb i).1)
  · have hrev : ∑ i : Fin (κ + 1), colW K U (Fin.rev i) = ∑ i : Fin (κ + 1), colW K U i :=
      Equiv.sum_comp Fin.revPerm (colW K U)
    have hs : ∑ i : Fin (κ + 1), (colW K U i + colW K U (Fin.rev i)) ≤ ∑ i : Fin (κ + 1), 4 * S :=
      Finset.sum_le_sum (fun i _ => hpair i)
    rw [Finset.sum_add_distrib, hrev] at hs
    have h4 : ∑ i : Fin (κ + 1), (4 * S) = ((κ : ℤ) + 1) * (4 * S) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    simp only [wt]
    linarith

end Formalism.HermitianLattices.ExplicitEstimates
