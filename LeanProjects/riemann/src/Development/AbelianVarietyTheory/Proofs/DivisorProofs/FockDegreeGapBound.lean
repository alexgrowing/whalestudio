import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.SixthReductionExplicit
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.FockDegreeGap

variable {D : D7} {L : SizeData₂ D}

theorem abs_sum_range_sub (g : ℕ → ℝ) (M : ℕ) (y c : ℝ) (h : ∀ r < M, |g r - y| ≤ c) :
    |(∑ r ∈ Finset.range M, g r) - M * y| ≤ M * c := by
  have e : (∑ r ∈ Finset.range M, g r) - M * y = ∑ r ∈ Finset.range M, (g r - y) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_card_nsmul (Finset.range M) (fun r => |g r - y|) c
    (fun r hr => h r (Finset.mem_range.1 hr))
  rwa [Finset.card_range, nsmul_eq_mul] at this

noncomputable def topWt (L : SizeData₂ D) (τ : D.what₂.Tau) : ℝ :=
  ∑ t : D.host.TT, if (D.eTau τ : D.R.GG) = D.R.tau1 t then (L.aT t : ℝ) else 0

theorem tau1_injective {φ : Formalism.HC.Frame} {t t' : φ.A} (h : φ.tau1 t = φ.tau1 t') : t = t' :=
  φ.iota_bijective.1 (congrArg Prod.snd h)

theorem topWt_top (L : SizeData₂ D) {τ : D.what₂.Tau} {t : D.host.TT}
    (h : (D.eTau τ : D.R.GG) = D.R.tau1 t) : topWt L τ = L.aT t := by
  unfold topWt
  rw [Finset.sum_eq_single t, if_pos h]
  · intro s _ hs
    exact if_neg fun h' => hs (Subtype.ext (tau1_injective (h'.symm.trans h)))
  · simp

theorem topWt_off (L : SizeData₂ D) {τ : D.what₂.Tau}
    (h : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces) : topWt L τ = 0 := by
  unfold topWt
  refine Finset.sum_eq_zero fun t _ => if_neg fun h' => h ?_
  unfold Host.topPlaces
  exact Finset.mem_image.2 ⟨t, t.2, h'.symm⟩

theorem sum_topWt (L : SizeData₂ D) : ∑ τ, topWt L τ = ∑ t : D.host.TT, (L.aT t : ℝ) := by
  unfold topWt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single (D.eTau.symm ⟨D.R.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩)]
  · simp
  · intro τ _ hτ
    refine if_neg fun h' => hτ ?_
    rw [Equiv.eq_symm_apply]
    exact Subtype.ext h'
  · simp

theorem wj_succ (D : D7) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    wj D (i + 1) τ = (((D.hc τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
  unfold wj
  rw [dif_pos (by simpa using hi)]
  rfl

theorem head_row (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : ℕ) (hr : r < D.R.k) :
    nuRow D u (i + 1) τ r ≤ (((D.hcW u τ).u ⟨r, hr⟩ : ℚ) : ℝ) + wj D (i + 1) τ ∧
    (((D.hcW u τ).u ⟨r, hr⟩ : ℚ) : ℝ) + wj D (i + 1) τ - D.R.N D.R.m ≤ nuRow D u (i + 1) τ r := by
  rw [RowWeightLemmas.nuRow_head D u i hi τ r hr, wj_succ D i hi, D.hcW_e]
  have h1 : r ≤ D.R.N i := by unfold Ranks.N; omega
  have h2 : D.R.N i + D.R.t ≤ D.R.N D.R.m := by
    unfold Ranks.N
    have := Nat.mul_le_mul_right (D.R.t + 1) (show i + 1 ≤ D.R.m from hi)
    rw [Nat.add_mul] at this
    omega
  have h1' : (r : ℝ) ≤ D.R.N i := by exact_mod_cast h1
  have h2' : (D.R.N i : ℝ) + D.R.t ≤ D.R.N D.R.m := by exact_mod_cast h2
  have h3 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  push_cast
  constructor <;> linarith

theorem block_row (L : SizeData₂ D) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : ℕ)
    (hk : D.R.k ≤ r) (hr : r < D.R.N i) : |nuRow D u (i + 1) τ r - 0| ≤ 2 * L.etaSz := by
  have h0 := RowWeightLemmas.nuRow_pos D u i hi τ r hr
  rw [sub_zero, abs_of_pos h0]
  obtain ⟨q, s, hq, hs, rfl⟩ := RowWeightLemmas.block_decomp D.R i r hk hr
  rw [RowWeightLemmas.nuRow_block D u i hi τ q s hq hs, D.hcW_e]
  have a1 := abs_le.1 (L.be_close τ ⟨i, hi⟩ ⟨i, hi⟩)
  have a2 := abs_le.1 (L.be_close τ ⟨i, hi⟩ ⟨q, by omega⟩)
  have a3 : (q : ℝ) ≤ i := by exact_mod_cast hq.le
  have a4 : (0 : ℝ) ≤ ((i : ℝ) - q) * ((D.R.t : ℝ) + 1) := mul_nonneg (by linarith) (by positivity)
  push_cast at a1 a2 ⊢
  linarith [a1.1, a2.2]

theorem nuAbs_place (P : ParameterChoice' D L) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau)
    (hw : 0 ≤ wj D (i + 1) τ) :
    |nuAbs D u (i + 1) τ - topWt L τ - ((D.R.k : ℝ) - 2) * wj D (i + 1) τ| ≤
      2 * wj D (i + 1) τ + 3 * D.R.k * (L.Sc + D.R.N D.R.m) + D.R.m * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) := by
  obtain ⟨n, hn⟩ : ∃ n, D.R.k = n + 2 := ⟨D.R.k - 2, by have := D.R.m_add_three_le_k; omega⟩
  have hn3 : 3 ≤ n := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.N (i + 1 - 1) = n + 1 + 1 + i * (D.R.t + 1) := by unfold Ranks.N; rw [hn]; rfl
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hkN : (D.R.k : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have hkn : (D.R.k : ℝ) = n + 2 := by exact_mod_cast hn
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  unfold nuAbs
  rw [hN, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∀ r < n, |nuRow D u (i + 1) τ (r + 1) - wj D (i + 1) τ| ≤ L.Sc + D.R.N D.R.m := by
    intro r hr
    obtain ⟨a1, a2⟩ := head_row u i hi τ (r + 1) (by omega)
    obtain ⟨b1, b2⟩ := L.cloud_u u τ ⟨r + 1, by omega⟩ (by show 1 ≤ r + 1; omega) (by show r + 1 + 1 < D.R.k; omega)
    rw [abs_le]
    constructor <;> linarith
  have s1 := abs_le.1 (abs_sum_range_sub _ n _ _ hmid)
  have s2 := abs_le.1 (abs_sum_range_sub (fun r => nuRow D u (i + 1) τ (n + 1 + 1 + r)) (i * (D.R.t + 1)) 0 _
    (fun r hr => block_row L u i hi τ _ (by omega) (by unfold Ranks.N; omega)))
  have s3 : 0 < nuRow D u (i + 1) τ (n + 1) := RowWeightLemmas.nuRow_pos D u i hi τ _ (by unfold Ranks.N; omega)
  have s4 : nuRow D u (i + 1) τ (n + 1) ≤ nuRow D u (i + 1) τ (0 + 1) :=
    RowWeightLemmas.nuRow_anti' D u i hi τ _ _ (by omega) (by unfold Ranks.N; omega)
  have s5 := (abs_le.1 (hmid 0 (by omega))).2
  have s6 : |nuRow D u (i + 1) τ 0 - topWt L τ| ≤ wj D (i + 1) τ + 3 * L.Sc + D.R.N D.R.m := by
    have hk0 : 0 < D.R.k := by omega
    obtain ⟨a1, a2⟩ := head_row u i hi τ 0 hk0
    rw [D.hcW_first u τ hk0] at a1 a2
    rw [abs_le]
    by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht⟩ := GlobalTheory.HCEntries.exists_top ha
      rw [topWt_top L ht]
      rw [(L.top_u τ t hk0 ht).1] at a1 a2
      constructor <;> linarith
    · rw [topWt_off L ha]
      have h1 := P.cloud_place_bound τ (by omega) ha
      have h2 := L.cloud_v τ ⟨0, by omega⟩
      have h3 := RowWeightLemmas.nuRow_pos D u i hi τ 0 (by unfold Ranks.N; omega)
      push_cast at h1
      constructor <;> linarith [h2.2]
  have s7 := abs_le.1 s6
  have hi' : (i : ℝ) ≤ D.R.m := by exact_mod_cast hi.le
  have s8 : (i : ℝ) * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) ≤ D.R.m * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) := by gcongr
  push_cast at s2
  have s9 : 0 ≤ (n : ℝ) * (L.Sc + D.R.N D.R.m) := by positivity
  rw [hkn, abs_le]
  constructor <;> nlinarith [s1.1, s1.2, s2.1, s2.2, s7.1, s7.2]

theorem eQ_succ (D : D7) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) : eQ D (i + 1) τ = (D.hc τ).e ⟨i, hi⟩ := by
  unfold eQ
  rw [dif_pos ⟨by omega, hi⟩]
  rfl

theorem ranks_le (D : D7) : (D.R.k : ℝ) + D.R.m ≤ D.R.N D.R.m ∧ (D.R.t : ℝ) + 1 ≤ D.R.N D.R.m := by
  have h1 : D.R.k + D.R.m ≤ D.R.N D.R.m := by
    unfold Ranks.N
    have : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h2 : D.R.t + 1 ≤ D.R.N D.R.m := by
    unfold Ranks.N
    have : D.R.t + 1 ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_left _ (by have := D.R.two_le_m; omega)
    omega
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem letters_place (L : SizeData₂ D) (hK : KapDef D) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau)
    (hw : 0 ≤ wj D (i + 1) τ) :
    |((((∑ a, |D.what₂.kaBig (i + 1) τ a|) + ∑ a, |D.what₂.kaSmall (i + 1) τ a| : ℤ)) : ℝ) -
        ((D.R.k : ℝ) - 1) * wj D (i + 1) τ| ≤
      D.R.k * (L.Sc + 2 * D.R.N D.R.m) + 2 * D.R.m * (L.etaSz + 2 * D.R.N D.R.m) := by
  obtain ⟨k1, k2⟩ := hK (i + 1) (by omega) hi τ
  obtain ⟨n, hn⟩ : ∃ n, D.R.k = n + 1 := ⟨D.R.k - 1, by have := D.R.m_add_three_le_k; omega⟩
  have hkn : (D.R.k : ℝ) = n + 1 := by exact_mod_cast hn
  obtain ⟨r1, r2⟩ := ranks_le D
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hi' : (i : ℝ) + 1 ≤ D.R.m := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have e1 : ((∑ a, |D.what₂.kaBig (i + 1) τ a| : ℤ) : ℝ) =
      ∑ r ∈ Finset.range (n + (i + 1)), |aPlus D (i + 1) τ r| := by
    rw [show n + (i + 1) = (D.R.sigW (i + 1)).1 by unfold Ranks.sigW; simp only; omega,
      ← Fin.sum_univ_eq_sum_range (fun r => |aPlus D (i + 1) τ r|)]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold aPlus
    rw [← k1 a, Rat.cast_intCast]
  have e2 : ((∑ a, |D.what₂.kaSmall (i + 1) τ a| : ℤ) : ℝ) =
      ∑ r ∈ Finset.range (D.R.m - (i + 1)), |aMinus D (i + 1) τ r| := by
    rw [show D.R.m - (i + 1) = (D.R.sigW (i + 1)).2 from rfl,
      ← Fin.sum_univ_eq_sum_range (fun r => |aMinus D (i + 1) τ r|)]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold aMinus
    rw [← abs_neg ((aMinusQ D (i + 1) τ a : ℚ) : ℝ), ← Rat.cast_neg, ← k2 a, Rat.cast_intCast]
  rw [Int.cast_add, e1, e2, Finset.sum_range_add]
  have s1 := abs_le.1 (abs_sum_range_sub (fun r => |aPlus D (i + 1) τ r|) n (wj D (i + 1) τ)
    (L.Sc + 2 * D.R.N D.R.m) (fun r hr => by
      have hr' : r < D.R.k - 1 := by omega
      have hr2 : (r : ℝ) + 1 ≤ n := by exact_mod_cast hr
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      obtain ⟨c1, c2⟩ := L.cloud_v τ ⟨r, hr'⟩
      have h1 : |aPlus D (i + 1) τ r - wj D (i + 1) τ| ≤ L.Sc + 2 * D.R.N D.R.m := by
        unfold aPlus
        rw [aPlusQ_eq, eQ_succ D i hi, wj_succ D i hi]
        unfold sigPar
        rw [dif_pos hr', abs_le]
        push_cast
        constructor <;> linarith
      refine le_trans ?_ h1
      have h2 := abs_abs_sub_abs_le_abs_sub (aPlus D (i + 1) τ r) (wj D (i + 1) τ)
      rwa [abs_of_nonneg hw] at h2))
  have s2 := abs_le.1 (abs_sum_range_sub (fun r => |aPlus D (i + 1) τ (n + r)|) (i + 1) 0
    (L.etaSz + 2 * D.R.N D.R.m) (fun r hr => by
      have hr2 : (r : ℝ) ≤ i := by exact_mod_cast Nat.lt_succ_iff.1 hr
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      have hb : n + r - (D.R.k - 1) < D.R.m := by omega
      have c := abs_le.1 (L.be_close τ ⟨_, hb⟩ ⟨i, hi⟩)
      simp only [sub_zero, abs_abs]
      unfold aPlus
      rw [aPlusQ_eq, eQ_succ D i hi]
      unfold sigPar
      rw [dif_neg (by omega), dif_pos hb, abs_le]
      push_cast at c ⊢
      constructor <;> linarith [c.1, c.2]))
  have s3 := abs_le.1 (abs_sum_range_sub (fun r => |aMinus D (i + 1) τ r|) (D.R.m - (i + 1)) 0
    (L.etaSz + 2 * D.R.N D.R.m) (fun r hr => by
      have hb : i + 1 + r < D.R.m := by omega
      have hr2 : (r : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : r ≤ D.R.m)
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      have c := abs_le.1 (L.be_close τ ⟨_, hb⟩ ⟨i, hi⟩)
      simp only [sub_zero, abs_abs]
      unfold aMinus aMinusQ
      rw [eQ_succ D i hi, dif_pos hb, abs_le]
      push_cast at c ⊢
      constructor <;> linarith [c.1, c.2]))
  have b1 : ((i + 1 : ℕ) : ℝ) * (L.etaSz + 2 * D.R.N D.R.m) ≤ D.R.m * (L.etaSz + 2 * D.R.N D.R.m) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hi) (by positivity)
  have b2 : ((D.R.m - (i + 1) : ℕ) : ℝ) * (L.etaSz + 2 * D.R.N D.R.m) ≤ D.R.m * (L.etaSz + 2 * D.R.N D.R.m) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (by positivity)
  rw [mul_zero] at s2 s3
  rw [hkn, abs_le]
  constructor <;> nlinarith [s1.1, s1.2, s2.1, s2.2, s3.1, s3.2]

theorem errors_le (h : SizesAt L) (P : ParameterChoice' D L) :
    (D.R.k : ℝ) * L.Sc ≤ L.sc.b ∧ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.b ∧
      (D.R.k : ℝ) * D.R.N D.R.m ≤ L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -, hS, -⟩ := h
  have hb' := GlobalTheory.HCEntries.b'_pos L
  have hbb : L.sc.b' ≤ L.sc.b := by linarith [GlobalTheory.HCEntries.b'_Sc_le hS, L.Sc_pos]
  have a6 : L.sc.w'' D.R.n ≤ L.sc.b' :=
    div_le_self hb'.le (one_le_mul_of_one_le_of_one_le L.sc.one_lt_alt.le (GlobalTheory.HCEntries.one_le_n D))
  refine ⟨by linarith [P.kS_le], by linarith [P.mteta], ?_⟩
  have he := (GlobalTheory.HCEntries.eta_k_le hE).1
  have h1 := P.h0_ge.2.2.2.2.1
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have h2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self L.etaSz_pos.le hm
  obtain ⟨r1, r2⟩ := ranks_le D
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hN : (1 : ℝ) ≤ D.R.N D.R.m := by linarith
  have h3 : (D.R.k : ℝ) * D.R.N D.R.m ≤ (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
  have h4 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
  have h5 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  linarith

end GlobalTheory.FockDegreeGap
