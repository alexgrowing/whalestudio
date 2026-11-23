import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Metric Set Topology

noncomputable section

namespace TorsionEquidistribution

theorem coe_intCast_eq_zero (k : ℤ) : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 :=
  (AddCircle.coe_eq_zero_iff 1).2 ⟨k, by simp⟩

theorem eq_zero_of_nsmul_eq_zero_of_norm_lt {m : ℕ} (hm : 0 < m) {y : AddCircle (1 : ℝ)}
    (hy : m • y = 0) (hn : ‖y‖ < 1 / m) : y = 0 := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hts : (QuotientAddGroup.mk t : AddCircle (1 : ℝ)) = ((t - round t : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_sub, coe_intCast_eq_zero, sub_zero]
  have hns : ‖((t - round t : ℝ) : AddCircle (1 : ℝ))‖ = |t - round t| := by
    rw [← hts]; exact UnitAddCircle.norm_eq
  rw [hts] at hy hn ⊢
  rw [hns] at hn
  rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hy
  obtain ⟨k, hk⟩ := hy
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hk' : (k : ℝ) = m * (t - round t) := by simpa using hk
  have habs : |(k : ℝ)| < 1 := by
    rw [hk', abs_mul, abs_of_pos hm']
    calc (m : ℝ) * |t - round t| < m * (1 / m) := mul_lt_mul_of_pos_left hn hm'
      _ = 1 := by field_simp
  have hk0 : k = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast habs)
  have hs0 : t - round t = 0 := by
    rw [hk0, Int.cast_zero] at hk'
    rcases mul_eq_zero.1 hk'.symm with h | h
    · exact absurd h hm'.ne'
    · exact h
  rw [hs0]; rfl

theorem one_div_le_dist {n m : ℕ} (hm : 0 < m) {x y : Fin n → AddCircle (1 : ℝ)}
    (hx : x ∈ torusTorsion n m) (hy : y ∈ torusTorsion n m) (hxy : x ≠ y) :
    1 / (m : ℝ) ≤ dist x y := by
  by_contra h
  rw [not_le] at h
  apply hxy
  funext i
  have hi : ‖x i - y i‖ < 1 / m := by
    rw [← dist_eq_norm]; exact lt_of_le_of_lt (dist_le_pi_dist x y i) h
  have hx' : m • x = 0 := hx
  have hy' : m • y = 0 := hy
  have h0 : m • (x i - y i) = 0 := by
    have h1 := congrFun hx' i
    have h2 := congrFun hy' i
    simp only [Pi.smul_apply, Pi.zero_apply] at h1 h2
    rw [smul_sub, h1, h2, sub_zero]
  exact sub_eq_zero.1 (eq_zero_of_nsmul_eq_zero_of_norm_lt hm h0 hi)

def gridPoint (n m : ℕ) (j : Fin n → ℤ) : Fin n → AddCircle (1 : ℝ) :=
  fun i => (((j i : ℝ) / m : ℝ) : AddCircle (1 : ℝ))

theorem gridPoint_mem {n m : ℕ} (hm : 0 < m) (j : Fin n → ℤ) :
    gridPoint n m j ∈ torusTorsion n m := by
  show m • gridPoint n m j = 0
  funext i
  simp only [gridPoint, Pi.smul_apply, Pi.zero_apply]
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul,
    mul_div_cancel₀ _ (Nat.cast_pos.2 hm).ne']
  exact coe_intCast_eq_zero _

theorem exists_gridPoint {n m : ℕ} (hm : 0 < m) {x : Fin n → AddCircle (1 : ℝ)}
    (hx : x ∈ torusTorsion n m) :
    ∃ j ∈ Fintype.piFinset (fun _ : Fin n => Finset.Ico (0 : ℤ) m), gridPoint n m j = x := by
  have hx' : m • x = 0 := hx
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have key : ∀ i, ∃ k : ℤ, 0 ≤ k ∧ k < m ∧
      ((((k : ℝ) / m : ℝ)) : AddCircle (1 : ℝ)) = x i := by
    intro i
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (x i)
    have h1 : m • x i = 0 := by simpa using congrFun hx' i
    rw [← ht] at h1
    change m • ((t : ℝ) : AddCircle (1 : ℝ)) = 0 at h1
    rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at h1
    obtain ⟨q, hq⟩ := h1
    have hq' : (q : ℝ) = m * t := by simpa using hq
    refine ⟨q % m, Int.emod_nonneg _ (by exact_mod_cast hm.ne'),
      Int.emod_lt_of_pos _ (by exact_mod_cast hm), ?_⟩
    have hd := Int.emod_add_ediv_mul q m
    have hdiv : ((q % (m : ℤ) : ℤ) : ℝ) / m = t - ((q / (m : ℤ) : ℤ) : ℝ) := by
      have hd' : ((q % (m : ℤ) : ℤ) : ℝ) + ((q / (m : ℤ) : ℤ) : ℝ) * (m : ℝ) = q := by
        exact_mod_cast hd
      rw [div_eq_iff hm'.ne']
      linear_combination hd' + hq'
    rw [hdiv, AddCircle.coe_sub, coe_intCast_eq_zero, sub_zero, ← ht]
  choose k hk0 hkm hk using key
  exact ⟨k, Fintype.mem_piFinset.2 fun i => Finset.mem_Ico.2 ⟨hk0 i, hkm i⟩, funext hk⟩

theorem gridPoint_injOn {n m : ℕ} (hm : 0 < m) {W : Fin n → Finset ℤ}
    (hW : ∀ i, ∀ a ∈ W i, ∀ b ∈ W i, |a - b| < m) :
    InjOn (gridPoint n m) (Fintype.piFinset W : Set (Fin n → ℤ)) := by
  intro j hj j' hj' h
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  funext i
  have hji := Fintype.mem_piFinset.1 (Finset.mem_coe.1 hj) i
  have hji' := Fintype.mem_piFinset.1 (Finset.mem_coe.1 hj') i
  have h1 := congrFun h i
  simp only [gridPoint] at h1
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h1
  obtain ⟨q, hq⟩ := h1
  have hq' : ((j i - j' i : ℤ) : ℝ) = ((q * m : ℤ) : ℝ) := by
    rw [zsmul_eq_mul, mul_one, div_sub_div_same, eq_div_iff hm'.ne'] at hq
    push_cast; linarith
  have hint : j i - j' i = q * m := by exact_mod_cast hq'
  have hlt := hW i _ hji _ hji'
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  rw [hint, abs_mul, abs_of_pos hmz] at hlt
  have hq1 : |q| < 1 := by nlinarith
  have hq0 : q = 0 := Int.abs_lt_one_iff.1 hq1
  rw [hq0, zero_mul, sub_eq_zero] at hint
  exact hint

theorem quarter_le_norm {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 3 / 4) :
    (1 / 4 : ℝ) ≤ ‖(t : AddCircle (1 : ℝ))‖ := by
  rw [UnitAddCircle.norm_eq]
  rcases le_or_gt (round t) 0 with h | h
  · have h' : (round t : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have h0 : (1 : ℤ) ≤ round t := h
    have h' : (1 : ℝ) ≤ round t := by exact_mod_cast h0
    rw [abs_of_nonpos (by linarith)]; linarith

theorem eventually_ncard_inter_lt {n : ℕ} (Z : Set (Fin n → AddCircle (1 : ℝ)))
    (hZ : IsClosed Z) (hZ0 : volume Z = 0) :
    ∀ᶠ m : ℕ in atTop, ((torusTorsion n m ∩ Z).ncard : ℝ) * 12 < (m : ℝ) ^ n := by
  set ε : ENNReal := ENNReal.ofReal ((2 / 3 : ℝ) ^ n / 12) with hε
  have hεpos : 0 < ε := ENNReal.ofReal_pos.2 (by positivity)
  have hlim : Tendsto (fun r : ℝ => volume (cthickening r Z)) (𝓝 0) (𝓝 0) := by
    have := tendsto_measure_cthickening_of_isClosed (μ := volume) (s := Z)
      ⟨1, one_pos, measure_ne_top _ _⟩ hZ
    rwa [hZ0] at this
  have hr : Tendsto (fun m : ℕ => (1 / 3 : ℝ) / m) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hev := (hlim.comp hr).eventually (gt_mem_nhds hεpos)
  filter_upwards [hev, eventually_ge_atTop 1] with m hvol hm1
  simp only [Function.comp_apply] at hvol
  have hm : 0 < m := hm1
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set r : ℝ := (1 / 3 : ℝ) / m with hrdef
  have hr0 : 0 < r := by positivity
  have hTfin : (torusTorsion n m).Finite := by
    refine ((Fintype.piFinset fun _ : Fin n => Finset.Ico (0 : ℤ) m).finite_toSet.image
      (gridPoint n m)).subset ?_
    intro x hx
    obtain ⟨j, hj, rfl⟩ := exists_gridPoint hm hx
    exact ⟨j, hj, rfl⟩
  have hSfin : (torusTorsion n m ∩ Z).Finite := hTfin.subset inter_subset_left
  set F := hSfin.toFinset with hF
  have hdisj : PairwiseDisjoint (F : Set (Fin n → AddCircle (1 : ℝ))) fun x => closedBall x r := by
    intro x hx y hy hxy
    simp only [hF, Set.Finite.coe_toFinset] at hx hy
    apply closedBall_disjoint_closedBall
    have := one_div_le_dist hm hx.1 hy.1 hxy
    have h2 : r + r < 1 / m := by
      rw [hrdef]; field_simp; norm_num
    linarith
  have hball : ∀ x : Fin n → AddCircle (1 : ℝ), volume (closedBall x r) = ENNReal.ofReal (2 * r) ^ n := by
    intro x
    rw [volume_pi_closedBall _ hr0.le]
    simp only [AddCircle.volume_closedBall]
    have : min (1 : ℝ) (2 * r) = 2 * r := by
      apply min_eq_right
      have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have h2 : (1 / 3 : ℝ) / m ≤ 1 / 3 := div_le_self (by norm_num) h1
      rw [hrdef]; linarith
    simp [this]
  have hsub : (⋃ x ∈ F, closedBall x r) ⊆ cthickening r Z := by
    intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨x, hx, hy⟩ := hy
    simp only [hF, Set.Finite.mem_toFinset] at hx
    exact closedBall_subset_cthickening hx.2 r hy
  have hsum : (F.card : ENNReal) * ENNReal.ofReal (2 * r) ^ n < ε := by
    calc (F.card : ENNReal) * ENNReal.ofReal (2 * r) ^ n
        = ∑ x ∈ F, volume (closedBall x r) := by simp [hball]
      _ = volume (⋃ x ∈ F, closedBall x r) :=
          (measure_biUnion_finset hdisj fun _ _ => measurableSet_closedBall).symm
      _ ≤ volume (cthickening r Z) := measure_mono hsub
      _ < ε := hvol
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), hε,
    ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hsum
  have hcard : (torusTorsion n m ∩ Z).ncard = F.card := by
    rw [hF, Set.ncard_eq_toFinset_card _ hSfin]
  rw [hcard]
  have h2r : 2 * r = (2 / 3) / m := by rw [hrdef]; ring
  rw [h2r, div_pow] at hsum
  have hmn : (0 : ℝ) < (m : ℝ) ^ n := by positivity
  have ha : (0 : ℝ) < (2 / 3 : ℝ) ^ n := by positivity
  rw [mul_div_assoc', div_lt_div_iff₀ hmn (by norm_num)] at hsum
  nlinarith

theorem proof : TorsionEquidistribution.Statement := by
  intro n hn Z c hZ hZ0 _hc
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  filter_upwards [eventually_ncard_inter_lt Z hZ hZ0, eventually_ge_atTop 12] with m hz hm12
  have hm : 0 < m := by omega
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hm12' : (12 : ℝ) ≤ m := by exact_mod_cast hm12
  set T := torusTorsion (k + 1) m with hT
  set i₀ : Fin (k + 1) := ⟨0, hn⟩ with hi₀
  set S := T ∩ Z with hS
  set G' := {x ∈ T \ Z | (1 / 4 : ℝ) ≤ ‖x i₀ + (c : AddCircle (1 : ℝ))‖} with hG'
  change (T \ Z).ncard ≤ 3 * G'.ncard

  have hTsub : T ⊆ gridPoint (k + 1) m ''
      (Fintype.piFinset fun _ : Fin (k + 1) => Finset.Ico (0 : ℤ) m) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := exists_gridPoint hm hx
    exact ⟨j, hj, rfl⟩
  have hTfin : T.Finite := ((Finset.finite_toSet _).image _).subset hTsub
  have hTcard : T.ncard ≤ m ^ (k + 1) := by
    refine (ncard_le_ncard hTsub ((Finset.finite_toSet _).image _)).trans ?_
    refine (ncard_image_le (Finset.finite_toSet _)).trans ?_
    rw [ncard_coe_finset, Fintype.card_piFinset]
    simp [Int.card_Ico]

  set G := {x ∈ T | (1 / 4 : ℝ) ≤ ‖x i₀ + (c : AddCircle (1 : ℝ))‖} with hG
  set a : ℤ := ⌈(m : ℝ) / 4 - m * c⌉ with ha
  set b : ℤ := ⌊3 * (m : ℝ) / 4 - m * c⌋ with hb
  have ha1 : (m : ℝ) / 4 - m * c ≤ a := Int.le_ceil _
  have ha2 : (a : ℝ) < (m : ℝ) / 4 - m * c + 1 := Int.ceil_lt_add_one _
  have hb1 : (b : ℝ) ≤ 3 * (m : ℝ) / 4 - m * c := Int.floor_le _
  have hb2 : 3 * (m : ℝ) / 4 - m * c < b + 1 := Int.lt_floor_add_one _
  set W : Fin (k + 1) → Finset ℤ := fun i => if i = i₀ then Finset.Icc a b else Finset.Ico 0 m
    with hW
  have hWwidth : ∀ i, ∀ u ∈ W i, ∀ v ∈ W i, |u - v| < m := by
    intro i u hu v hv
    by_cases hi : i = i₀
    · simp only [hW, hi, if_true, Finset.mem_Icc] at hu hv
      have h1 : ((b - a : ℤ) : ℝ) < m := by push_cast; linarith
      have h2 : b - a < m := by exact_mod_cast h1
      rw [abs_lt]; constructor <;> omega
    · simp only [hW, hi, if_false, Finset.mem_Ico] at hu hv
      rw [abs_lt]; constructor <;> omega
  have hGsub : gridPoint (k + 1) m '' (Fintype.piFinset W) ⊆ G := by
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨gridPoint_mem hm j, ?_⟩
    have hj0 := Fintype.mem_piFinset.1 (Finset.mem_coe.1 hj) i₀
    simp only [hW, if_true, Finset.mem_Icc] at hj0
    have hlo : (a : ℝ) ≤ j i₀ := by exact_mod_cast hj0.1
    have hhi : (j i₀ : ℝ) ≤ b := by exact_mod_cast hj0.2
    have e : gridPoint (k + 1) m j i₀ + (c : AddCircle (1 : ℝ)) =
        (((j i₀ : ℝ) / m + c : ℝ) : AddCircle (1 : ℝ)) := by
      rw [AddCircle.coe_add]; rfl
    rw [e]
    apply quarter_le_norm
    · have h1 : (1 / 4 - c) * m ≤ j i₀ := by linarith
      have := (le_div_iff₀ hm').2 h1; linarith
    · have h1 : (j i₀ : ℝ) ≤ (3 / 4 - c) * m := by linarith
      have := (div_le_iff₀ hm').2 h1; linarith
  have hGfin : G.Finite := hTfin.subset fun x hx => hx.1
  have hGcard : (b + 1 - a).toNat * m ^ k ≤ G.ncard := by
    calc (b + 1 - a).toNat * m ^ k = (Fintype.piFinset W).card := by
          have hW0 : W 0 = Finset.Icc a b := if_pos (Fin.ext (by simp [hi₀]))
          have hWs : ∀ i : Fin k, W i.succ = Finset.Ico (0 : ℤ) m := fun i =>
            if_neg (fun h => by simp [hi₀, Fin.ext_iff] at h)
          rw [Fintype.card_piFinset, Fin.prod_univ_succ, hW0]
          simp only [hWs, Int.card_Icc, Int.card_Ico, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, sub_zero, Int.toNat_natCast]
      _ = (gridPoint (k + 1) m '' (Fintype.piFinset W)).ncard := by
          rw [(gridPoint_injOn hm hWwidth).ncard_image, ncard_coe_finset]
      _ ≤ G.ncard := ncard_le_ncard hGsub hGfin

  have hSfin : S.Finite := hTfin.subset inter_subset_left
  have hG'fin : G'.Finite := hTfin.subset fun x hx => hx.1.1
  have hGG' : G.ncard ≤ G'.ncard + S.ncard := by
    refine (ncard_le_ncard_sdiff_add_ncard G S hSfin).trans (Nat.add_le_add_right ?_ _)
    refine ncard_le_ncard ?_ hG'fin
    rintro x ⟨⟨hxT, hx⟩, hxS⟩
    exact ⟨⟨hxT, fun hxZ => hxS ⟨hxT, hxZ⟩⟩, hx⟩
  have hT'card : (T \ Z).ncard ≤ T.ncard := ncard_le_ncard sdiff_subset hTfin

  have hP : (0 : ℝ) ≤ (m : ℝ) ^ k := by positivity
  have hab : ((b + 1 - a : ℤ) : ℝ) ≤ (((b + 1 - a).toNat : ℕ) : ℝ) := by
    exact_mod_cast Int.self_le_toNat _
  have h1 : ((m : ℝ) / 2 - 1) * (m : ℝ) ^ k ≤ G.ncard := by
    calc ((m : ℝ) / 2 - 1) * (m : ℝ) ^ k ≤ ((b + 1 - a : ℤ) : ℝ) * (m : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (by push_cast; linarith) hP
      _ ≤ (((b + 1 - a).toNat : ℕ) : ℝ) * (m : ℝ) ^ k := mul_le_mul_of_nonneg_right hab hP
      _ ≤ G.ncard := by exact_mod_cast hGcard
  have h2 : 0 ≤ ((m : ℝ) - 12) * (m : ℝ) ^ k := mul_nonneg (by linarith) hP
  have h3 : ((T \ Z).ncard : ℝ) ≤ (m : ℝ) ^ k * m := by
    rw [← pow_succ]; exact_mod_cast hT'card.trans hTcard
  have h4 : (G.ncard : ℝ) ≤ G'.ncard + S.ncard := by exact_mod_cast hGG'
  rw [pow_succ] at hz
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  nlinarith

end TorsionEquidistribution

end

end GroundTheory.Heights₂.Heights
