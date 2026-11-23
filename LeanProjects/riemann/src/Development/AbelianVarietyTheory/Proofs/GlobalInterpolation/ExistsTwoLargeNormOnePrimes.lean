import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivLeRpowThreeQuarters

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem excluded_count_lt {Y r : ℝ} (hY : 1 ≤ Y) (hr : 1 ≤ r) (h : 20 * r ^ 3 < Y ^ ((3 : ℝ) / 20)) :
    (3 * r + 1) * (1 + 2 * r ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) < Y ^ ((9 : ℝ) / 10) := by
  have hP : 1 ≤ Y ^ ((3 : ℝ) / 4) := Real.one_le_rpow hY (by norm_num)
  have hs : Y ^ ((9 : ℝ) / 10) = Y ^ ((3 : ℝ) / 20) * Y ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  rw [hs]
  generalize Y ^ ((3 : ℝ) / 4) = P at hP ⊢
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have h1 : 1 ≤ r ^ 2 * P := one_le_mul_of_one_le_of_one_le hr2 hP
  have h2 : r ^ 2 ≤ r ^ 2 * P := le_mul_of_one_le_right (by positivity) hP
  have h3 : 1 + 2 * r ^ 2 * (P + 1) ≤ 5 * (r ^ 2 * P) := by nlinarith
  calc (3 * r + 1) * (1 + 2 * r ^ 2 * (P + 1)) ≤ (4 * r) * (5 * (r ^ 2 * P)) :=
        mul_le_mul (by linarith) h3 (by positivity) (by positivity)
    _ = 20 * r ^ 3 * P := by ring
    _ < _ := mul_lt_mul_of_pos_right h (by linarith)

theorem exists_pair_disjoint_exceptional {Y : ℝ} {r : ℕ} (hY : 2 ≤ Y) (hr : 1 ≤ r)
    (h : 20 * (r : ℝ) ^ 3 < Y ^ ((3 : ℝ) / 20)) (G : Finset ℕ) (hG : ∀ g ∈ G, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y)
    (hc : Y ^ ((9 : ℝ) / 10) ≤ G.card) :
    ∃ a ∈ G, ∃ b ∈ G, a ≠ b ∧ Disjoint (Formalism.CyclotomicNorms.BB r a) (Formalism.CyclotomicNorms.BB r b) := by
  have hpos : 0 < Y ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
  have hne : G.Nonempty := Finset.card_pos.1 (by exact_mod_cast hpos.trans_le hc)
  obtain ⟨a, ha⟩ := hne
  have hex : ∃ b ∈ G, ¬ (Formalism.CyclotomicNorms.BB r b ∩ Formalism.CyclotomicNorms.BB r a).Nonempty := by
    by_contra hcon
    push Not at hcon
    have h1 := GlobalTheory.choice_count Y r a hY hr (hG a ha).1 (hG a ha).2 G
      (fun g hg => ⟨(hG g hg).1, (hG g hg).2, hcon g hg⟩)
    have h2 := excluded_count_lt (Y := Y) (r := r) (by linarith) (by exact_mod_cast hr) h
    linarith
  obtain ⟨b, hb, hab⟩ := hex
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · rintro rfl
    exact hab ⟨a, Or.inl rfl, Or.inl rfl⟩
  · rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
    exact Set.not_nonempty_iff_eq_empty.1 hab

theorem two_type_primes : NormPrimes → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (N d : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → ModRow s N d → ∃ g : Fin 2 → ℕ, (∀ i, (g i).Prime ∧ ((R.k : ℝ) * s.b) ^ 8 ≤ (g i : ℝ) ∧ (g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8 ∧ NormOne d N (g i)) ∧ g 0 ≠ g 1 ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (g 0)) (Formalism.CyclotomicNorms.BB R.r (g 1)) := by
  classical
  intro hN eps he0 he1
  obtain ⟨x1, h1⟩ := hN eps he0 he1
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps 16 1 he0 one_pos
  obtain ⟨x3, h3⟩ := rank_basic_bounds eps he0 he1
  refine ⟨max (max x1 x2) (max x3 21), fun s R q d hs hx hR hq => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  have hc := h1 s R q d hs hx1 hR hq
  have hb := (h2 s hs hx2).2.2.1
  obtain ⟨-, -, hr5, hkr, -⟩ := h3 s R hs hx3 hR
  have hmk := R.m_add_three_le_k
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have hx0 : 0 < s.x := by linarith
  have hX : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  rw [Real.rpow_one, show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hb
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hr5
  have hb1 : s.x ^ 16 ≤ s.b := (le_mul_of_one_le_right (by positivity) hX).trans hb
  have hx15 : 1 ≤ s.x ^ 15 := one_le_pow₀ (by linarith)
  have hx16 : 21 * s.x ^ 15 ≤ s.x ^ 16 := by
    rw [pow_succ s.x 15, mul_comm]; exact mul_le_mul_of_nonneg_left hx4 (by linarith)
  have hb2 : 2 ≤ s.b := by linarith
  have hkb : s.b ≤ (R.k : ℝ) * s.b := le_mul_of_one_le_left (by linarith) hk1
  have hkb1 : 1 ≤ (R.k : ℝ) * s.b := by linarith
  have hY : 2 ≤ ((R.k : ℝ) * s.b) ^ 8 :=
    (hb2.trans hkb).trans (le_self_pow₀ hkb1 (by norm_num))
  have hr3 : (R.r : ℝ) ^ 3 ≤ s.x ^ 15 := by
    calc (R.r : ℝ) ^ 3 ≤ (s.x ^ 5) ^ 3 := pow_le_pow_left₀ (by positivity) hr5 3
      _ = _ := by ring
  have hZ : (R.k : ℝ) * s.b ≤ (((R.k : ℝ) * s.b) ^ 8) ^ ((3 : ℝ) / 20) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.self_le_rpow_of_one_le hkb1 (by norm_num)
  obtain ⟨a, ha, b, hb', hab, hd⟩ := exists_pair_disjoint_exceptional (r := R.r) hY (by omega)
    (by linarith) _ (fun g hg => by
      rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by linarith)] at hg
      exact ⟨hg.2.2.1, hg.1⟩) hc
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by linarith)] at ha hb'
  refine ⟨![a, b], ?_, hab, hd⟩
  intro i
  fin_cases i
  · exact ⟨ha.2.1, ha.2.2.1, ha.1, ha.2.2.2⟩
  · exact ⟨hb'.2.1, hb'.2.2.1, hb'.1, hb'.2.2.2⟩

end GlobalTheory.EX
