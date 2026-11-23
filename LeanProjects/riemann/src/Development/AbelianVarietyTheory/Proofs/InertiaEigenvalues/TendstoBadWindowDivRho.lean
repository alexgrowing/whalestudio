import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticesIdempotentPositionBoundedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RhoPowLowerBoundSwappedPairsStatement

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

open Classical in

noncomputable def badWinBox {ι : Type} (S I : Finset ι) (L k : ℕ) (i₀ i : ι) : Finset ℤ :=
  if i ∈ S then (if i ∈ I then Finset.Icc (2 * (k : ℤ) - L) (2 * k + L) else Finset.Icc (-(L : ℤ)) L)
  else if i = i₀ then Finset.Ico (-(L : ℤ)) L ∪ Finset.Ioc (2 * (k : ℤ) - L) (2 * k + L)
  else Finset.Icc (-(L : ℤ)) (2 * k + L)

open Classical in
theorem card_badWinBox_le {ι : Type} (S I : Finset ι) (L k : ℕ) (i₀ i : ι) :
    (badWinBox S I L k i₀ i).card ≤
      2 * (2 * L + 1) * (if i ∈ insert i₀ S then 1 else k + 1) := by
  unfold badWinBox
  by_cases hS : i ∈ S
  · have : i ∈ insert i₀ S := Finset.mem_insert_of_mem hS
    rw [if_pos hS, if_pos this]
    split_ifs <;> simp [Int.card_Icc] <;> omega
  · rw [if_neg hS]
    by_cases h0 : i = i₀
    · subst h0
      rw [if_pos rfl, if_pos (Finset.mem_insert_self _ _)]
      refine (Finset.card_union_le _ _).trans ?_
      simp [Int.card_Ico, Int.card_Ioc]; omega
    · rw [if_neg h0, if_neg (by simp [h0, hS])]
      simp [Int.card_Icc]
      nlinarith

open Classical in
theorem card_piFinset_badWinBox_le {ι : Type} [Fintype ι] (S I : Finset ι) (L k : ℕ) (i₀ : ι) (h₀ : i₀ ∉ S) :
    (Fintype.piFinset (badWinBox S I L k i₀)).card ≤
      (2 * (2 * L + 1)) ^ Fintype.card ι * (k + 1) ^ (Fintype.card ι - S.card - 1) := by
  rw [Fintype.card_piFinset]
  refine (Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => card_badWinBox_le S I L k i₀ i).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_ite, Finset.prod_const_one,
    one_mul, Finset.prod_const]
  have : (Finset.univ.filter fun i => i ∉ insert i₀ S).card = Fintype.card ι - S.card - 1 := by
    have h : (Finset.univ.filter fun i => i ∉ insert i₀ S) = (insert i₀ S)ᶜ := by ext; simp
    rw [h, Finset.card_compl, Finset.card_insert_of_notMem h₀]; omega
  rw [this]

end GlobalTheory.UnitLemma.Desc

namespace GlobalTheory.UnitLemma.Desc

theorem tendsto_badWindow_div_rho : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ (I I' : Finset ι), (∀ i ∈ S, i ∈ I ∨ i ∈ I') → ∀ (N L : ℕ) (D : ℚ) (f : ℕ → Submodule K.O B.A → ℚ), (∀ M ∈ B.Lin, ∃ p, Pos B a e N M p) → (∀ k M, |f k M| ≤ D) → (∀ k, L ≤ k → ∀ M ∈ B.Lin, ∀ p, Pos B a e N M p → f k M ≠ 0 → Win I I' L k p ∧ ¬ Mid S L k p) → Tendsto (fun k : ℕ => ((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop (𝓝 0) := by
  intro K B ι _ e π S a hsep ha hfr I I' hI N L D f hpos hD hsupp
  classical
  obtain ⟨C, hC⟩ := GlobalTheory.T.card_lattices_idempotent_position_bounded K B ι e π S a hsep ha hfr N
  have hrho := GlobalTheory.T.rho_pow_lower_bound_swappedPairs K B ι e π S a hsep ha hfr
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD 0 ⊥)
  set n := Fintype.card ι
  set m := n - S.card
  set A : ℕ := 2 * (2 * L + 1)
  have key : ∀ k, L ≤ k → |∑ᶠ M ∈ B.Lin, f k M| ≤ D * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℚ) := by
    intro k hk
    let W : Finset (ι → ℤ) :=
      (Finset.univ.filter (· ∉ S)).biUnion fun i₀ => Fintype.piFinset (badWinBox S I L k i₀)
    have hWcard : W.card ≤ m * A ^ n * (k + 1) ^ (m - 1) := by
      refine Finset.card_biUnion_le.trans ?_
      have h1 : ∀ i₀ ∈ Finset.univ.filter (· ∉ S),
          (Fintype.piFinset (badWinBox S I L k i₀)).card ≤ A ^ n * (k + 1) ^ (m - 1) := by
        intro i₀ hi₀
        exact card_piFinset_badWinBox_le S I L k i₀ (Finset.mem_filter.1 hi₀).2
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_const, smul_eq_mul]
      have h2 : (Finset.univ.filter (· ∉ S)).card = m := by
        have h : (Finset.univ.filter (· ∉ S)) = Sᶜ := by ext; simp
        rw [h, Finset.card_compl]
      rw [h2, mul_assoc]
    have hmem : ∀ M ∈ B.Lin, f k M ≠ 0 → ∃ p ∈ W, Pos B a e N M p := by
      intro M hM hf
      obtain ⟨p, hp⟩ := hpos M hM
      obtain ⟨hw, hmid⟩ := hsupp k hk M hM p hp hf
      refine ⟨p, ?_, hp⟩
      simp only [W, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      unfold Mid at hmid
      push_neg at hmid
      obtain ⟨i₀, hi₀, h₀⟩ := hmid
      refine ⟨i₀, hi₀, fun i => ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := hw i
      unfold badWinBox
      by_cases hS : i ∈ S
      · rw [if_pos hS]
        by_cases hiI : i ∈ I
        · rw [if_pos hiI]; simp only [Finset.mem_Icc]; exact ⟨h3 hiI, h2⟩
        · rw [if_neg hiI]
          have := (hI i hS).resolve_left hiI
          simp only [Finset.mem_Icc]; exact ⟨h1, h4 this⟩
      · rw [if_neg hS]
        by_cases h0 : i = i₀
        · subst h0
          rw [if_pos rfl]
          simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ioc]
          by_cases hl : (L : ℤ) ≤ p i
          · exact Or.inr ⟨h₀ hl, h2⟩
          · exact Or.inl ⟨h1, lt_of_not_ge hl⟩
        · rw [if_neg h0]; simp only [Finset.mem_Icc]; exact ⟨h1, h2⟩
    let T : Finset (Submodule K.O B.A) := W.biUnion fun p => (hC p).1.toFinset
    have hTcard : T.card ≤ W.card * C := by
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_sum fun p _ => ?_).trans (by rw [Finset.sum_const, smul_eq_mul])
      rw [← Set.ncard_eq_toFinset_card _ (hC p).1]
      exact (hC p).2
    have hfs : ∑ᶠ M ∈ B.Lin, f k M = ∑ M ∈ T.filter (· ∈ B.Lin), f k M := by
      apply finsum_mem_eq_sum_of_inter_support_eq
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Finset.coe_filter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hM, hf⟩
        refine ⟨⟨?_, hM⟩, hf⟩
        obtain ⟨p, hpW, hp⟩ := hmem M hM hf
        simp only [T, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        exact ⟨p, hpW, hp⟩
      · rintro ⟨⟨_, hM⟩, hf⟩
        exact ⟨hM, hf⟩
    rw [hfs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun M _ => hD k M).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hD0
    have : (T.filter (· ∈ B.Lin)).card ≤ m * A ^ n * (k + 1) ^ (m - 1) * C :=
      (Finset.card_filter_le _ _).trans (hTcard.trans (Nat.mul_le_mul_right _ hWcard))
    exact_mod_cast this
  have hm : ∀ k : ℕ, m * (k + 1) ^ (m - 1) * (k + 1) = m * (k + 1) ^ m := by
    intro k
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel h]
  set c : ℝ := (D : ℝ) * (A : ℝ) ^ n * (m : ℝ) * (C : ℝ)
  have hlim : Tendsto (fun k : ℕ => c * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop L] with k hk
  have hr : ((k + 1 : ℕ) : ℝ) ^ m ≤ (B.rho (algebraMap K.O B.A a ^ k) : ℝ) := by exact_mod_cast hrho k
  have hpos' : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ m := by positivity
  have hk' := key k hk
  have hk'' : |((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ)| ≤ (D : ℝ) * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hk'
    push_cast at this ⊢
    simpa [Rat.cast_abs] using this
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
  rw [div_le_iff₀ (lt_of_lt_of_le hpos' hr)]
  calc |((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ)|
      ≤ (D : ℝ) * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℝ) := hk''
    _ = c * (1 / ((k : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ m := by
        have h := congrArg (fun x : ℕ => (x : ℝ)) (hm k)
        push_cast at h ⊢
        field_simp
        simp only [c]
        linear_combination (D : ℝ) * (A : ℝ) ^ n * (C : ℝ) * h
    _ ≤ c * (1 / ((k : ℝ) + 1)) * (B.rho (algebraMap K.O B.A a ^ k) : ℝ) := by
        refine mul_le_mul_of_nonneg_left hr ?_
        simp only [c]; positivity

end GlobalTheory.UnitLemma.Desc
