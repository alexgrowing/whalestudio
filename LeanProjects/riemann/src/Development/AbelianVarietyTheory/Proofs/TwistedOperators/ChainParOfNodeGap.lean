import Mathlib
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianParamOppositeSignEntriesDistGeGap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare GlobalTheory.Chain.ParOfSizes

namespace GlobalTheory.Chain.ParOfNodeGap

theorem minSig_lamS_le {D : D7} (k : Fin D.R.m) (τ : D.what₂.Tau) : minSig (lamS D k τ) ≤ D.R.m := by
  unfold minSig
  refine (min_le_right _ _).trans ?_
  calc ((lamS D k τ).filter fun x => x.2 = false).card
      ≤ (Finset.univ.image fun i : Fin D.R.m =>
          ((val (D.hc τ) (k : ℕ) (Sum.inr (Sum.inl i)) + (D.hc τ).e k : ℚ), false)).card := by
        apply Finset.card_le_card
        rintro ⟨a, s⟩ hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hx, hs⟩ := hx
        simp only at hs
        subst hs
        obtain ⟨y, hy, hsy⟩ := (mem_lamS k τ a false).1 hx
        rcases y with y | y | y
        · simp [sgn] at hsy
        · exact Finset.mem_image.2 ⟨y, Finset.mem_univ _, by rw [hy]⟩
        · simp [sgn] at hsy
    _ ≤ (Finset.univ : Finset (Fin D.R.m)).card := Finset.card_image_le
    _ = D.R.m := by simp

theorem num_bound' {n q m N : ℕ} (hq : q ≤ m) (hn : n ≤ N) (hm : 2 ≤ m) (hN : 3 * m ^ 2 ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 * (N : ℝ) ^ 3 := by
  have hqm : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ (2 : ℕ) := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h
        rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
        positivity
      · rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le
        · exact Nat.one_le_cast.mpr h
        · norm_num
    refine h1.trans ?_
    have : (q : ℝ) ≤ m := by exact_mod_cast hq
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hNR : 3 * (m : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hN12 : (12 : ℝ) ≤ N := by nlinarith
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (m : ℝ) ^ 2 :=
        mul_le_mul (by linarith) hqm hpos (by positivity)
    _ ≤ 120 * (N : ℝ) * ((N : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 40 * (N : ℝ) ^ 2 := by ring
    _ ≤ 4 * (N : ℝ) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (by linarith : (0 : ℝ) ≤ N - 10)]

private theorem le_sub_b_succ_of_nodeGap {D : D7} {h : ℝ} (H : D.NodeGap h) (τ : D.what₂.Tau) :
    ∀ (i : ℕ) (hi : i + 1 < D.R.m), h ≤ (((D.hc τ).b ⟨i + 1, hi⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) := by
  intro i hi
  have := H D.u₀ τ i hi
  rwa [D.hcW_base] at this

private theorem rankY_le_N (D : D7) {j : ℕ} (hj : j ≤ D.R.m) : D.R.rankY j ≤ D.R.N D.R.m := by
  have h1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul hj le_rfl
  simp only [Ranks.rankY, Ranks.r, Ranks.N]
  rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem three_mul_m_sq_le_N (D : D7) : 3 * D.R.m ^ 2 ≤ D.R.N D.R.m := by
  have h1 : 3 * D.R.m + 1 ≤ D.R.t := D.R.three_m_lt_t
  have h2 : D.R.m * (3 * D.R.m + 1) ≤ D.R.m * D.R.t := Nat.mul_le_mul le_rfl h1
  simp only [Ranks.N]
  nlinarith

theorem stepGap_of_nodeGap {D : D7} (h : D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6))
    (k : Fin D.R.m) : StepGap D k := by
  set H : ℝ := 4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6 with hH
  have hg := le_sub_b_succ_of_nodeGap h
  have hNpos : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcube : ∀ j : ℕ, j ≤ D.R.m → ((D.R.rankY j : ℕ) : ℝ) ^ 3 < H := by
    intro j hj
    have : ((D.R.rankY j : ℕ) : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := by exact_mod_cast rankY_le_N D hj
    have : ((D.R.rankY j : ℕ) : ℝ) ^ 3 ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) this 3
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    nlinarith [pow_nonneg hNpos 3]
  intro τ
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamT k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamT k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    refine le_trans ?_ (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
    have hb := num_bound' (minSig_lamS_le k τ) (rankY_le_N D k.isLt.le) D.R.two_le_m (three_mul_m_sq_le_N D)
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith

theorem chainPar_of_nodeGap :
    ∀ D : D7, D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6) → ∀ k, GlobalTheory.Chain.ChainPar D k := by
  intro D h k
  exact (chainPar_iff_stepGap k).mpr (stepGap_of_nodeGap h k)

end GlobalTheory.Chain.ParOfNodeGap

end
