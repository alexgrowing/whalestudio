import Mathlib
import Formalism.DropLevelBounds.Statement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WtAddSingle
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators

noncomputable section

namespace GlobalTheory.UnitCase

variable {C : Type} [Field C] {σ κ : Type}

lemma coeff_mul_pow_eq_zero {a b : MvPowerSeries σ C} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (j k : ℕ) (m : σ →₀ ℕ) (h : m.degree < j + k) :
    MvPowerSeries.coeff m (a ^ j * b ^ k) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ MvPowerSeries.le_order_mul
  refine lt_of_lt_of_le ?_ (add_le_add (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero j ha)
    (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hb))
  exact_mod_cast h

lemma coeff_mvExp_eq {a : MvPowerSeries σ C} (ha : MvPowerSeries.constantCoeff a = 0)
    (m : σ →₀ ℕ) (N : ℕ) (h : m.degree < N) :
    MvPowerSeries.coeff m (mvExp a) =
      ∑ k ∈ Finset.range N, MvPowerSeries.coeff m (a ^ k) / (k.factorial : C) := by
  change ∑ k ∈ Finset.range (m.degree + 1), _ = _
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at *
    omega
  · intro k _ hk
    simp only [Finset.mem_range] at hk
    have := coeff_mul_pow_eq_zero ha ha k 0 m (by omega)
    rw [pow_zero, mul_one] at this
    rw [this, zero_div]

lemma mvExp_add [CharZero C] {a b : MvPowerSeries σ C} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : mvExp (a + b) = mvExp a * mvExp b := by
  classical
  ext m
  set N := m.degree + 1 with hN
  have hR : MvPowerSeries.coeff m (mvExp a * mvExp b) =
      ∑ p ∈ Finset.range N ×ˢ Finset.range N,
        MvPowerSeries.coeff m (a ^ p.1 * b ^ p.2) / ((p.1.factorial : C) * p.2.factorial) := by
    rw [MvPowerSeries.coeff_mul]
    simp only [MvPowerSeries.coeff_mul, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hd : q.1.degree + q.2.degree = m.degree := by rw [← hq, map_add]
    rw [coeff_mvExp_eq ha q.1 N (by omega), coeff_mvExp_eq hb q.2 N (by omega),
      Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [div_mul_div_comm]
  rw [hR, coeff_mvExp_eq (by rw [map_add, ha, hb, add_zero]) m N (by omega)]
  rw [← Finset.sum_filter_of_ne (p := fun p : ℕ × ℕ => p.1 + p.2 ∈ Finset.range N)]
  · rw [← Finset.sum_fiberwise_eq_sum_filter]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have : (Finset.range N ×ˢ Finset.range N).filter (fun p : ℕ × ℕ => p.1 + p.2 = k) =
        Finset.HasAntidiagonal.antidiagonal k := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
      omega
    rw [this, (Commute.all a b).add_pow', map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_nsmul, nsmul_eq_mul, ← hp, Nat.cast_add_choose C]
    have h1 : ((p.1 + p.2).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : ((p.1).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h3 : ((p.2).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  · intro p _ hp
    rw [Finset.mem_range]
    by_contra hc
    exact hp (by rw [coeff_mul_pow_eq_zero ha hb _ _ m (by omega), zero_div])

lemma coeff_zero_mvExp (a : MvPowerSeries σ C) : MvPowerSeries.coeff 0 (mvExp a) = 1 := by
  change ∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), _ = _
  simp

lemma mvExp_zero' : mvExp (0 : MvPowerSeries σ C) = 1 := by
  classical
  ext m
  rw [coeff_mvExp_eq (map_zero _) m (m.degree + 1) (by omega), Finset.sum_range_succ']
  simp

lemma mvExp_sum [CharZero C] {ι : Type} (s : Finset ι) (a : ι → MvPowerSeries σ C)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    mvExp (∑ i ∈ s, a i) = ∏ i ∈ s, mvExp (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvExp_zero']
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, mvExp_add (ha i) (by simp [map_sum, ha]), ih]

lemma asc_mod (l b k : ℕ) :
    (((l * b + 1).ascFactorial k : ℕ) : ZMod l) = (k.factorial : ZMod l) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.ascFactorial_succ, Nat.factorial_succ, Nat.cast_mul, ih]
    simp [add_comm]

lemma wilson_pow {l : ℕ} (hl : l.Prime) (b : ℕ) :
    ∃ w : ℤ, ((l * b).factorial : ℤ) = (-(l : ℤ)) ^ b * w ∧ (w : ZMod l) = (b.factorial : ZMod l) := by
  haveI := Fact.mk hl
  induction b with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ b ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨-((b : ℤ) + 1) * ((l * b + 1).ascFactorial (l - 1) : ℕ) * w, ?_, ?_⟩
    · have e : l * (b + 1) = (l * b + (l - 1)) + 1 := by
        have := hl.one_le
        rw [mul_add]; omega
      have e2 : (l * (b + 1)).factorial =
          l * (b + 1) * ((l * b).factorial * (l * b + 1).ascFactorial (l - 1)) := by
        rw [Nat.factorial_mul_ascFactorial]
        conv_lhs => rw [e, Nat.factorial_succ, ← e]
      rw [e2, Nat.cast_mul, Nat.cast_mul ((l * b).factorial), h1]
      push_cast
      ring
    · rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, asc_mod, h2, ZMod.wilsons_lemma,
        Nat.factorial_succ]
      push_cast
      ring

lemma mfact_eq [Fintype κ] (A : κ →₀ ℕ) : mfact A = ∏ j, (A j).factorial :=
  Finsupp.prod_fintype _ _ (by simp)

lemma mfact_int [Fintype κ] {l : ℕ} (hl : l.Prime) (A β : κ →₀ ℕ) (h : ∀ j, l * β j ≤ A j) :
    ∃ z : ℤ, (mfact A : ℤ) = (-(l : ℤ)) ^ (∑ j, β j) * z := by
  have : ∀ j, ∃ z : ℤ, ((A j).factorial : ℤ) = (-(l : ℤ)) ^ (β j) * z := by
    intro j
    obtain ⟨w, hw, -⟩ := wilson_pow hl (β j)
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial (h j)
    exact ⟨w * t, by rw [ht, Nat.cast_mul, hw, mul_assoc]⟩
  choose z hz using this
  refine ⟨∏ j, z j, ?_⟩
  rw [mfact_eq, Nat.cast_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => hz j

lemma mfact_smul [Fintype κ] {l : ℕ} (hl : l.Prime) (β : κ →₀ ℕ) :
    ∃ w : ℤ, (mfact (l • β) : ℤ) = (-(l : ℤ)) ^ (∑ j, β j) * w ∧
      (w : ZMod l) = (mfact β : ZMod l) := by
  choose z hz hz' using fun j => wilson_pow hl (β j)
  refine ⟨∏ j, z j, ?_, ?_⟩
  · rw [mfact_eq, Nat.cast_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => hz j
  · rw [mfact_eq, Nat.cast_prod, Int.cast_prod]
    exact Finset.prod_congr rfl fun j _ => hz' j

lemma not_dvd_mfact [Fintype κ] {l : ℕ} (hl : l.Prime) (β : κ →₀ ℕ) (h : ∀ j, β j < l) :
    ¬ l ∣ mfact β := by
  rw [mfact_eq, Prime.dvd_finset_prod_iff hl.prime]
  rintro ⟨j, -, hj⟩
  exact absurd (hl.dvd_factorial.1 hj) (not_le.2 (h j))

lemma coeff_pow_zmod {l : ℕ} (hl : l.Prime) (q : MvPolynomial κ ℤ) (A : κ →₀ ℕ) :
    ((MvPolynomial.coeff A (q ^ l) : ℤ) : ZMod l) =
      MvPolynomial.coeff A (MvPolynomial.expand l (MvPolynomial.map (Int.castRingHom (ZMod l)) q)) := by
  haveI := Fact.mk hl
  rw [MvPolynomial.expand_zmod, ← map_pow, MvPolynomial.coeff_map]
  rfl

lemma prod_eq_monomial [Fintype κ] (l : ℕ) (B : κ →₀ ℕ) :
    ∏ j, ((MvPowerSeries.X (Sum.inl j) : MvPowerSeries (κ ⊕ κ) C) ^ l *
      MvPowerSeries.X (Sum.inr j)) ^ (B j) =
      MvPowerSeries.monomial (Finsupp.sumElim (l • B) B) 1 := by
  classical
  have : ∀ (s : Finset κ) (f : κ → (κ ⊕ κ) →₀ ℕ),
      ∏ j ∈ s, (MvPowerSeries.monomial (f j) (1 : C)) =
        MvPowerSeries.monomial (∑ j ∈ s, f j) 1 := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPowerSeries.monomial_mul_monomial,
        one_mul]
  simp only [mul_pow, ← pow_mul]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [this]
  congr 2
  ext (x | x)
  · simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
  · simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

def mainTerm [Fintype κ] (l : ℕ) (c : C) : MvPowerSeries (κ ⊕ κ) C :=
  c • ∑ j, MvPowerSeries.X (Sum.inl j) ^ l * MvPowerSeries.X (Sum.inr j)

lemma sumElim_inj {A B A' B' : κ →₀ ℕ} (h : Finsupp.sumElim A B = Finsupp.sumElim A' B') :
    A = A' ∧ B = B' :=
  ⟨Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inl j),
    Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inr j)⟩

lemma coeff_mainTerm_pow [Fintype κ] [DecidableEq κ] (l : ℕ) (c : C) (k : ℕ) (A B : κ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.sumElim A B) (mainTerm l c ^ k) =
      if A = l • B ∧ ∑ j, B j = k then c ^ k * Nat.multinomial Finset.univ B else 0 := by
  rw [mainTerm, smul_pow, Finset.sum_pow_eq_sum_piAntidiag, map_smul, map_sum, smul_eq_mul]
  have key : ∀ f : κ → ℕ, MvPowerSeries.coeff (Finsupp.sumElim A B)
      ((Nat.multinomial Finset.univ f : MvPowerSeries (κ ⊕ κ) C) *
        ∏ j, ((MvPowerSeries.X (Sum.inl j) : MvPowerSeries (κ ⊕ κ) C) ^ l *
          MvPowerSeries.X (Sum.inr j)) ^ (f j)) =
      if f = B then (if A = l • B then (Nat.multinomial Finset.univ B : C) else 0) else 0 := by
    intro f
    obtain ⟨f, rfl⟩ := (Finsupp.equivFunOnFinite (α := κ) (M := ℕ)).surjective f
    simp only [Finsupp.equivFunOnFinite_apply]
    rw [prod_eq_monomial, ← nsmul_eq_mul, map_nsmul, MvPowerSeries.coeff_monomial]
    by_cases h1 : f = B
    · subst h1
      by_cases h2 : A = l • f
      · subst h2
        simp [Finsupp.equivFunOnFinite]
      · rw [if_neg fun h => h2 (sumElim_inj h).1]
        simp [h2]
    · rw [if_neg fun h => h1 (sumElim_inj h).2.symm, if_neg, smul_zero]
      intro h
      exact h1 (Finsupp.ext fun j => congrFun h j)
  simp only [key]
  rw [Finset.sum_ite_eq']
  by_cases h1 : A = l • B <;> by_cases h2 : ∑ j, B j = k <;> simp [h1, h2]

lemma coeff_exp_mainTerm [CharZero C] [Fintype κ] [DecidableEq κ] (l : ℕ) (c : C)
    (A B : κ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.sumElim A B) (mvExp (mainTerm l c)) =
      if A = l • B then c ^ (∑ j, B j) * (mfact B : C)⁻¹ else 0 := by
  change ∑ k ∈ Finset.range ((Finsupp.sumElim A B).degree + 1), _ = _
  simp only [coeff_mainTerm_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single (∑ j, B j)]
    · rw [if_pos ⟨h, rfl⟩, ← Nat.multinomial_spec, ← mfact_eq]
      have h1 : (Nat.multinomial Finset.univ B : C) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.multinomial_pos _ _).ne'
      push_cast
      field_simp
    · intro k _ hk
      rw [if_neg fun h' => hk h'.2.symm, zero_div]
    · intro hk
      exfalso
      apply hk
      rw [Finset.mem_range, Finsupp.degree_eq_sum, Fintype.sum_sum_type]
      simp only [Finsupp.sumElim_inr]
      omega
  · simp [h]

lemma exists_sumElim (m : κ ⊕ κ →₀ ℕ) : ∃ A B : κ →₀ ℕ, m = Finsupp.sumElim A B :=
  ⟨m.comapDomain Sum.inl Sum.inl_injective.injOn, m.comapDomain Sum.inr Sum.inr_injective.injOn,
    by ext (x | x) <;> simp⟩

def mult (O : Subring C) (l : ℕ) : AddSubgroup C :=
  O.toAddSubgroup.map (AddMonoidHom.mulLeft (l : C))

lemma mem_mult {O : Subring C} {l : ℕ} {x : C} : x ∈ mult O l ↔ ∃ o ∈ O, (l : C) * o = x :=
  Iff.rfl

lemma coeff_mul_mfact [Fintype κ] {l : ℕ} (hl : l.Prime) (q : MvPolynomial κ ℤ) (A β : κ →₀ ℕ)
    (h : ∀ j, l * β j ≤ A j) (hne : A ≠ l • β) :
    ∃ z : ℤ, MvPolynomial.coeff A (q ^ l) * (mfact A : ℤ) = (-(l : ℤ)) ^ (∑ j, β j) * (l * z) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, A j ≠ l * β j := by
    by_contra hc
    push Not at hc
    exact hne (Finsupp.ext fun j => by simpa using hc j)
  by_cases hd : l ∣ A j
  · obtain ⟨z, hz⟩ := mfact_int hl A (β + Finsupp.single j 1) fun i => by
      by_cases hi : j = i
      · subst hi
        obtain ⟨t, ht⟩ := hd
        have h1 := h j
        rw [ht] at h1 hj ⊢
        have h2 : β j ≤ t := Nat.le_of_mul_le_mul_left h1 hl.pos
        have h3 : t ≠ β j := fun e => hj (by rw [e])
        refine Nat.mul_le_mul_left _ ?_
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        omega
      · simpa [Finsupp.single_apply, hi] using h i
    have hs : ∑ i, (β + Finsupp.single j 1 : κ →₀ ℕ) i = ∑ i, β i + 1 := by
      simp [Finset.sum_add_distrib, Finsupp.single_apply]
    refine ⟨-(MvPolynomial.coeff A (q ^ l) * z), ?_⟩
    rw [hz, hs]
    ring
  · obtain ⟨z, hz⟩ := mfact_int hl A β h
    have h0 := coeff_pow_zmod hl q A
    rw [MvPolynomial.coeff_expand_of_not_dvd _ hd, ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    obtain ⟨t, ht⟩ := h0
    refine ⟨t * z, ?_⟩
    rw [hz, ht]
    ring

lemma neg_pow_mul_inv [CharZero C] {l : ℕ} (hl : l.Prime) (k : ℕ) :
    (-(l : C)) ^ k * (-(l : C)⁻¹) ^ k = 1 := by
  have : (l : C) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  rw [← mul_pow, neg_mul_neg, mul_inv_cancel₀ this, one_pow]

lemma offDiag_mem [CharZero C] [Fintype κ] {l : ℕ} (hl : l.Prime) (O : Subring C)
    (hO : ∀ n : ℕ, ¬ l ∣ n → (n : C)⁻¹ ∈ O) (q : MvPolynomial κ ℤ) (t : ℤ) (A B : κ →₀ ℕ)
    (hB : ∀ j, B j < l) (hAB : ∑ j, A j = l * ∑ j, B j) (G : MvPowerSeries (κ ⊕ κ) C)
    (hG0 : MvPowerSeries.coeff 0 G = 1)
    (hG : ∀ m ≤ Finsupp.sumElim A B, MvPowerSeries.coeff m G ∈ O) :
    ((MvPolynomial.coeff A (q ^ l) : ℤ) : C) * t * ((mfact A : C) * mfact B) *
        MvPowerSeries.coeff (Finsupp.sumElim A B) (mvExp (mainTerm l (-(l : C)⁻¹)) * G) -
      ((MvPolynomial.coeff A (q ^ l) : ℤ) : C) * t * ((mfact A : C) * mfact B) *
        MvPowerSeries.coeff (Finsupp.sumElim A B) (mvExp (mainTerm l (-(l : C)⁻¹))) ∈
      mult O l := by
  classical
  have hmem : (Finsupp.sumElim A B, (0 : κ ⊕ κ →₀ ℕ)) ∈
      Finset.HasAntidiagonal.antidiagonal (Finsupp.sumElim A B) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal, add_zero]
  rw [MvPowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ hmem, hG0, mul_one, mul_add,
    add_sub_cancel_left, Finset.mul_sum]
  refine sum_mem ?_
  rintro ⟨p, r⟩ hpr
  rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hpr
  obtain ⟨hne, hsum⟩ := hpr
  obtain ⟨A₁, β, rfl⟩ := exists_sumElim p
  simp only at hsum ⊢
  rw [coeff_exp_mainTerm]
  split_ifs with h
  swap
  · simp
  subst h
  have h1 : ∀ j, l * β j ≤ A j := fun j => by
    have := DFunLike.congr_fun hsum (Sum.inl j)
    simp at this
    omega
  have h2 : ∀ j, β j ≤ B j := fun j => by
    have := DFunLike.congr_fun hsum (Sum.inr j)
    simp at this
    omega
  have h3 : A ≠ l • β := by
    rintro rfl
    have h4 : ∑ j, β j = ∑ j, B j := by
      apply Nat.eq_of_mul_eq_mul_left hl.pos
      rw [← hAB, Finset.mul_sum]
      simp
    have h5 : β = B := Finsupp.ext fun j =>
      (Finset.sum_eq_sum_iff_of_le fun i _ => h2 i).1 h4 j (Finset.mem_univ j)
    subst h5
    exact hne (by rw [left_eq_add.1 hsum.symm])
  obtain ⟨z, hz⟩ := coeff_mul_mfact hl q A β h1 h3
  have hz' : ((MvPolynomial.coeff A (q ^ l) : ℤ) : C) * (mfact A : C) =
      (-(l : C)) ^ (∑ j, β j) * (l * z) := by exact_mod_cast congrArg (Int.cast : ℤ → C) hz
  refine ⟨(z : C) * t * mfact B * (mfact β : C)⁻¹ * MvPowerSeries.coeff r G, ?_, ?_⟩
  · exact O.mul_mem (O.mul_mem (O.mul_mem (O.mul_mem (intCast_mem O z) (intCast_mem O t))
      (natCast_mem O _)) (hO _ (not_dvd_mfact hl β fun j => (h2 j).trans_lt (hB j))))
      (hG r (hsum ▸ le_add_self))
  · have := neg_pow_mul_inv (C := C) hl (∑ j, β j)
    change (l : C) * _ = _
    linear_combination
      (-(t * mfact B * (mfact β : C)⁻¹ * MvPowerSeries.coeff r G * (-(l : C)⁻¹) ^ (∑ j, β j))) * hz'
        - ((l : C) * z * t * mfact B * (mfact β : C)⁻¹ * MvPowerSeries.coeff r G) * this

lemma diag_mem [CharZero C] [Fintype κ] {l : ℕ} (hl : l.Prime) (O : Subring C)
    (q : MvPolynomial κ ℤ) (B : κ →₀ ℕ) :
    (∑ A ∈ (q ^ l).support, ((MvPolynomial.coeff A (q ^ l) : ℤ) : C) *
        (MvPolynomial.coeff B q : ℤ) * ((mfact A : C) * mfact B) *
        MvPowerSeries.coeff (Finsupp.sumElim A B) (mvExp (mainTerm l (-(l : C)⁻¹)))) -
      ((MvPolynomial.coeff B q : ℤ) : C) * mfact B * (MvPolynomial.coeff B q : ℤ) ∈ mult O l := by
  classical
  simp only [coeff_exp_mainTerm]
  rw [Finset.sum_eq_single (l • B), if_pos rfl]
  · obtain ⟨w, hw, hw'⟩ := mfact_smul hl B
    have h0 := coeff_pow_zmod hl q (l • B)
    rw [MvPolynomial.coeff_expand_smul _ hl.ne_zero, MvPolynomial.coeff_map, eq_intCast] at h0
    have h1 : ((MvPolynomial.coeff (l • B) (q ^ l) * w - MvPolynomial.coeff B q * mfact B : ℤ) :
        ZMod l) = 0 := by
      push_cast
      rw [h0, hw', sub_self]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    obtain ⟨z, hz⟩ := h1
    have hz' : ((MvPolynomial.coeff (l • B) (q ^ l) : ℤ) : C) * w -
        ((MvPolynomial.coeff B q : ℤ) : C) * mfact B = l * z := by
      exact_mod_cast congrArg (Int.cast : ℤ → C) hz
    have hw2 : (mfact (l • B) : C) = (-(l : C)) ^ (∑ j, B j) * w := by
      exact_mod_cast congrArg (Int.cast : ℤ → C) hw
    have h3 := neg_pow_mul_inv (C := C) hl (∑ j, B j)
    have h4 : (mfact B : C) * (mfact B : C)⁻¹ = 1 := by
      refine mul_inv_cancel₀ (Nat.cast_ne_zero.2 ?_)
      rw [mfact_eq]
      exact Finset.prod_ne_zero_iff.2 fun j _ => Nat.factorial_ne_zero _
    refine ⟨(z : C) * (MvPolynomial.coeff B q : ℤ),
      O.mul_mem (intCast_mem O _) (intCast_mem O _), ?_⟩
    change (l : C) * _ = _
    rw [hw2]
    generalize ((MvPolynomial.coeff (l • B) (q ^ l) : ℤ) : C) = a at *
    generalize ((MvPolynomial.coeff B q : ℤ) : C) = b at *
    generalize (-(l : C)) ^ (∑ j, B j) = c at *
    generalize (-(l : C)⁻¹) ^ (∑ j, B j) = d at *
    linear_combination (-b) * hz' - (a * b * w) * h3 - (a * b * w * c * d) * h4
  · intro A _ hA
    rw [if_neg hA, mul_zero]
  · intro h
    rw [MvPolynomial.notMem_support_iff.1 h]
    simp

lemma jetAt0_eq_sum (P : MvPolynomial σ C) (G : MvPowerSeries σ C) (s : Finset (σ →₀ ℕ))
    (hs : P.support ⊆ s) :
    jetAt0 P G = ∑ m ∈ s, MvPolynomial.coeff m P * (mfact m : C) * MvPowerSeries.coeff m G := by
  unfold jetAt0
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm]
  simp

lemma jetAt0_add (P Q : MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (P + Q) G = jetAt0 P G + jetAt0 Q G := by
  classical
  rw [jetAt0_eq_sum (P + Q) G (P.support ∪ Q.support) MvPolynomial.support_add,
    jetAt0_eq_sum P G (P.support ∪ Q.support) Finset.subset_union_left,
    jetAt0_eq_sum Q G (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

lemma jetAt0_sum {α : Type} (s : Finset α) (P : α → MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (∑ a ∈ s, P a) G = ∑ a ∈ s, jetAt0 (P a) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jetAt0]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, jetAt0_add, ih]

lemma jetAt0_monomial (m : σ →₀ ℕ) (c : C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.monomial m c) G = c * (mfact m : C) * MvPowerSeries.coeff m G := by
  classical
  rw [jetAt0_eq_sum _ G {m} MvPolynomial.support_monomial_subset]
  simp

lemma jetAt0_rename_mul [Fintype κ] (p q : MvPolynomial κ ℤ) (G : MvPowerSeries (κ ⊕ κ) C) :
    jetAt0 (MvPolynomial.rename Sum.inl (MvPolynomial.map (Int.castRingHom C) p) *
        MvPolynomial.rename Sum.inr (MvPolynomial.map (Int.castRingHom C) q)) G =
      ∑ A ∈ p.support, ∑ B ∈ q.support,
        ((MvPolynomial.coeff A p : ℤ) : C) * (MvPolynomial.coeff B q : ℤ) *
          ((mfact A : C) * mfact B) * MvPowerSeries.coeff (Finsupp.sumElim A B) G := by
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [map_sum, Finset.sum_mul_sum, jetAt0_sum, MvPolynomial.map_monomial,
    MvPolynomial.rename_monomial, MvPolynomial.monomial_mul, jetAt0_monomial,
    ← Finsupp.sumElim_eq_add, eq_intCast]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  congr 2
  rw [mfact_eq, mfact_eq, mfact_eq, Fintype.prod_sum_type, Nat.cast_mul]
  simp

lemma jet_sub_mem [CharZero C] [Fintype κ] {l : ℕ} (hl : l.Prime) (O : Subring C)
    (hO : ∀ n : ℕ, ¬ l ∣ n → (n : C)⁻¹ ∈ O) (q : MvPolynomial κ ℤ)
    (hB : ∀ B ∈ q.support, ∀ j, B j < l)
    (hAB : ∀ A ∈ (q ^ l).support, ∀ B ∈ q.support, ∑ j, A j = l * ∑ j, B j)
    (G : MvPowerSeries (κ ⊕ κ) C) (hG0 : MvPowerSeries.coeff 0 G = 1)
    (hG : ∀ A ∈ (q ^ l).support, ∀ B ∈ q.support,
      ∀ m ≤ Finsupp.sumElim A B, MvPowerSeries.coeff m G ∈ O) :
    jetAt0 (MvPolynomial.rename Sum.inl (MvPolynomial.map (Int.castRingHom C) (q ^ l)) *
        MvPolynomial.rename Sum.inr (MvPolynomial.map (Int.castRingHom C) q))
        (mvExp (mainTerm l (-(l : C)⁻¹)) * G) -
      ∑ B ∈ q.support, ((MvPolynomial.coeff B q : ℤ) : C) * mfact B *
        (MvPolynomial.coeff B q : ℤ) ∈ mult O l := by
  have h1 := sum_mem fun A hA => sum_mem fun B hB' =>
    offDiag_mem hl O hO q (MvPolynomial.coeff B q) A B (hB B hB') (hAB A hA B hB') G hG0
      (hG A hA B hB')
  have h2 := sum_mem (t := q.support) fun B _ => diag_mem hl O q B
  have h3 := add_mem h1 h2
  simp only [Finset.sum_sub_distrib] at h3
  rw [Finset.sum_comm (s := q.support), sub_add_sub_cancel] at h3
  rwa [jetAt0_rename_mul]

lemma row_det_pow (n k : ℕ) (A : Fin n × Fin n →₀ ℕ) (hA : A ∈ (cayDet n ℤ ^ k).support)
    (b : Fin n) : ∑ c, A (b, c) = k := by
  have h : (cayDet n ℤ).IsWeightedHomogeneous
      (fun x : Fin n × Fin n => if x.1 = b then 1 else 0) 1 := by
    rw [cayDet, Matrix.det_apply]
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun τ _ => ?_
    have h1 := MvPolynomial.IsWeightedHomogeneous.prod (R := ℤ)
      (w := fun x : Fin n × Fin n => if x.1 = b then 1 else 0) Finset.univ
      (fun i : Fin n => MvPolynomial.X (τ i, i)) (fun i => if τ i = b then 1 else 0)
      (fun i _ => MvPolynomial.isWeightedHomogeneous_X _ _ _)
    have h2 : ∑ i : Fin n, (if τ i = b then 1 else 0) = 1 := by
      rw [Equiv.sum_comp τ fun i => if i = b then 1 else 0]
      simp
    rw [h2] at h1
    rw [Units.smul_def]
    exact (MvPolynomial.weightedHomogeneousSubmodule ℤ _ 1).smul_mem _ h1
  have h3 := (h.pow k) (MvPolynomial.mem_support_iff.1 hA)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type,
    Finset.sum_eq_single b] at h3
  · simpa using h3
  · intro b' _ hb
    simp [hb]
  · simp

lemma map_cayDet (n : ℕ) : MvPolynomial.map (Int.castRingHom C) (cayDet n ℤ) = cayDet n C := by
  rw [cayDet, cayDet, RingHom.map_det]
  congr 1
  ext1 i j
  simp [Matrix.mvPolynomialX]

lemma detL_eq (n : ℕ) : detL C n = MvPolynomial.rename Sum.inl (cayDet n C) := by
  rw [detL, cayDet, AlgHom.map_det]
  congr 1
  ext1 i j
  simp [Matrix.mvPolynomialX]

lemma detR_eq (n : ℕ) : detR C n = MvPolynomial.rename Sum.inr (cayDet n C) := by
  rw [detR, cayDet, AlgHom.map_det]
  congr 1
  ext1 i j
  simp [Matrix.mvPolynomialX]

def intRing (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    change 0 ≤ v (a * b)
    rw [v.map_mul]
    exact add_nonneg ha hb
  one_mem' := v.map_one.ge
  add_mem' ha hb := v.map_le_add ha hb
  zero_mem' := by
    change 0 ≤ v 0
    rw [v.map_zero]
    exact le_top
  neg_mem' {a} ha := by
    change 0 ≤ v (-a)
    rwa [v.map_neg]

lemma val_nat {v : AddValuation C (WithTop ℝ)} {l : ℕ}
    (hp : ∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) (n : ℕ) (hn : ¬ l ∣ n) : v (n : C) = 0 := by
  induction n using induction_on_primes with
  | zero => simp at hn
  | one => simp
  | prime_mul p a hpp ih =>
    rw [Nat.cast_mul, v.map_mul, hp p hpp (by rintro rfl; exact hn (dvd_mul_right _ _)),
      ih fun h => hn (h.mul_left _), add_zero]

lemma inv_mem_intRing [CharZero C] {v : AddValuation C (WithTop ℝ)} {l : ℕ}
    (hp : ∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) (n : ℕ) (hn : ¬ l ∣ n) :
    (n : C)⁻¹ ∈ intRing v := by
  have h0 : (n : C) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; simp at hn)
  have := v.map_mul (n : C) (n : C)⁻¹
  rw [mul_inv_cancel₀ h0, v.map_one, val_nat hp n hn, zero_add] at this
  exact this.le

lemma val_prod_factorial {v : AddValuation C (WithTop ℝ)} {l : ℕ} (hl : l.Prime)
    (hp : ∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ c ∈ s, f c < l) : v (∏ c ∈ s, ((f c).factorial : C)) = 0 := by
  rw [← Nat.cast_prod]
  refine val_nat hp _ ?_
  rw [Prime.dvd_finset_prod_iff hl.prime]
  rintro ⟨j, hj, hj'⟩
  exact absurd (hl.dvd_factorial.1 hj') (not_le.2 (hf j hj))

theorem ubUnit : UBUnit := by
  intro C _ _ v l hl h5 hvl hp n n0 y hn hy h1 h10 hint
  classical
  set q := cayDet n0 ℤ ^ y with hq
  have hrB : ∀ B ∈ q.support, ∀ b, ∑ c, B (b, c) = y := fun B hB => row_det_pow n0 y B hB
  have hrA : ∀ A ∈ (q ^ l).support, ∀ b, ∑ c, A (b, c) = l * y := fun A hA => by
    rw [hq, ← pow_mul, mul_comm] at hA
    exact row_det_pow n0 _ A hA
  have key := jet_sub_mem hl (intRing v) (inv_mem_intRing hp) q
    (fun B hB j => by
      have h2 : B (j.1, j.2) ≤ ∑ c, B (j.1, c) :=
        Finset.single_le_sum (f := fun c => B (j.1, c)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j.2)
      rw [hrB B hB] at h2
      change B (j.1, j.2) < l
      omega)
    (fun A hA B hB => by
      simp only [Fintype.sum_prod_type, hrA A hA, hrB B hB, Finset.mul_sum])
    (mvExp h1) (coeff_zero_mvExp h1)
    (fun A hA B hB m hm => hint m
      (fun b => by
        rw [← hrA A hA b]
        exact Finset.sum_le_sum fun c _ => by simpa using hm (Sum.inl (b, c)))
      (fun b => by
        rw [← hrB B hB b]
        exact Finset.sum_le_sum fun c _ => by simpa using hm (Sum.inr (b, c))))
  have hmain : hP C l 1 n0 h1 = mainTerm l (-(l : C)⁻¹) + h1 := by
    simp [hP, mainTerm, expE, Fintype.sum_prod_type]
  have hL : LamP C l 1 n0 h1 y =
      jetAt0 (MvPolynomial.rename Sum.inl (MvPolynomial.map (Int.castRingHom C) (q ^ l)) *
        MvPolynomial.rename Sum.inr (MvPolynomial.map (Int.castRingHom C) q))
        (mvExp (mainTerm l (-(l : C)⁻¹)) * mvExp h1) := by
    rw [LamP, hmain, mvExp_add _ h10, detL_eq, detR_eq, hq, ← pow_mul, mul_comm y l, pow_one]
    · simp only [map_pow, map_cayDet]
    · simp [mainTerm]
  rw [← hL] at key
  obtain ⟨o, ho, he⟩ := mem_mult.1 key
  have hcap := GlobalTheory.DetPowPairing.main C n0 y
  have hsum : (∑ A ∈ (cayDet n0 C ^ y).support, MvPolynomial.coeff A (cayDet n0 C ^ y) *
      (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n0 C ^ y)) =
      ∑ B ∈ q.support, ((MvPolynomial.coeff B q : ℤ) : C) * mfact B *
        (MvPolynomial.coeff B q : ℤ) := by
    rw [← map_cayDet, ← map_pow, ← hq,
      MvPolynomial.support_map_of_injective _ (RingHom.injective_int _)]
    refine Finset.sum_congr rfl fun B _ => ?_
    simp [MvPolynomial.coeff_map, mfact, Finsupp.prod]
  rw [hsum] at hcap
  have hv := congrArg v hcap
  rw [v.map_mul, val_prod_factorial hl hp _ (fun c => c) (fun c hc => by
      have := Finset.mem_range.1 hc
      omega),
    val_prod_factorial hl hp _ (fun c => y + c) (fun c hc => by
      have := Finset.mem_range.1 hc
      omega), zero_add] at hv
  rw [eq_add_of_sub_eq' he.symm, v.map_add_eq_of_lt_left, hv]
  rw [hv, v.map_mul, hvl]
  exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right ho)

lemma le_weight_of_coeff_pow (w : (σ →₀ ℕ) → ℕ) (hw : ∀ a b, w (a + b) = w a + w b)
    {h : MvPowerSeries σ C} (hh : ∀ p, MvPowerSeries.coeff p h ≠ 0 → 1 ≤ w p) (k : ℕ) :
    ∀ p, MvPowerSeries.coeff p (h ^ k) ≠ 0 → k ≤ w p := by
  classical
  induction k with
  | zero => exact fun _ _ => Nat.zero_le _
  | succ k ih =>
    intro p hp
    rw [pow_succ, MvPowerSeries.coeff_mul] at hp
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [← hx, hw]
    exact add_le_add (ih _ (left_ne_zero_of_mul hne)) (hh _ (right_ne_zero_of_mul hne))

def intBelow (O : Subring C) (m : σ →₀ ℕ) : Submonoid (MvPowerSeries σ C) where
  carrier := {F | ∀ p ≤ m, MvPowerSeries.coeff p F ∈ O}
  one_mem' p _ := by
    classical
    rw [MvPowerSeries.coeff_one]
    split_ifs
    exacts [O.one_mem, O.zero_mem]
  mul_mem' {F G} hF hG p hp := by
    classical
    rw [MvPowerSeries.coeff_mul]
    refine sum_mem fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    exact O.mul_mem (hF _ ((hx ▸ le_self_add).trans hp)) (hG _ ((hx ▸ le_add_self).trans hp))

lemma degL_eq_row {n : ℕ} {p : PVar n →₀ ℕ} {b : Fin n} (h : ∀ x ∈ p.support, rowOf x = b) :
    degL p = rowDegZ p b := by
  refine Finset.sum_eq_single b (fun b' _ hb => Finset.sum_eq_zero fun c _ => ?_) (by simp)
  by_contra h0
  exact hb (h _ (Finsupp.mem_support_iff.2 h0))

lemma degR_eq_row {n : ℕ} {p : PVar n →₀ ℕ} {b : Fin n} (h : ∀ x ∈ p.support, rowOf x = b) :
    degR p = rowDegZ' p b := by
  refine Finset.sum_eq_single b (fun b' _ hb => Finset.sum_eq_zero fun c _ => ?_) (by simp)
  by_contra h0
  exact hb (h _ (Finsupp.mem_support_iff.2 h0))

lemma constantCoeff_eq_zero {v : AddValuation C (WithTop ℝ)} {l n0 : ℕ}
    {h1 : MvPowerSeries (PVar n0) C} (H : MplusRows v l n0 h1) :
    MvPowerSeries.constantCoeff h1 = 0 := by
  by_contra h
  have := H.2.1 0 h
  simp [degR] at this

theorem ubIntegral : UBIntegral := by
  intro C _ _ v l hl h5 hvl hp n0 y hy h1 H m hm hm'
  classical
  let hb : Fin n0 → MvPowerSeries (PVar n0) C := fun b p =>
    if ∀ x ∈ p.support, rowOf x = b then MvPowerSeries.coeff p h1 else 0
  have hbc : ∀ b p, MvPowerSeries.coeff p (hb b) =
      if ∀ x ∈ p.support, rowOf x = b then MvPowerSeries.coeff p h1 else 0 := fun _ _ => rfl
  have hdec : h1 = ∑ b, hb b := by
    ext p
    rw [map_sum]
    simp only [hbc]
    by_cases h0 : MvPowerSeries.coeff p h1 = 0
    · simp [h0]
    · obtain ⟨b, hb'⟩ := H.1 p h0
      rw [Finset.sum_eq_single b, if_pos hb']
      · intro b' _ hne
        rw [if_neg]
        intro h
        have hp0 : p ≠ 0 := by
          rintro rfl
          exact h0 (constantCoeff_eq_zero H)
        obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.2 hp0
        exact hne ((h x hx).symm.trans (hb' x hx))
      · simp
  have hb0 : ∀ b, MvPowerSeries.constantCoeff (hb b) = 0 := by
    intro b
    change MvPowerSeries.coeff 0 (hb b) = 0
    rw [hbc, if_pos (by simp)]
    exact constantCoeff_eq_zero H
  have hZ : ∀ p ≤ m, ∀ b, rowDegZ p b ≤ l * y := fun p hpm b =>
    le_trans (Finset.sum_le_sum fun c _ => hpm _) (hm b)
  have hZ' : ∀ p ≤ m, ∀ b, rowDegZ' p b ≤ y := fun p hpm b =>
    le_trans (Finset.sum_le_sum fun c _ => hpm _) (hm' b)
  have hint : ∀ b, hb b ∈ intBelow (intRing v) m := by
    intro b p hpm
    rw [hbc]
    split_ifs with h
    · refine H.2.2 p ?_ ?_
      · rw [degL_eq_row h, sq]
        exact (hZ p hpm b).trans_lt (Nat.mul_lt_mul_of_pos_left hy hl.pos)
      · rw [degR_eq_row h]
        exact (hZ' p hpm b).trans_lt hy
    · exact zero_mem _
  have hexp : ∀ b, mvExp (hb b) ∈ intBelow (intRing v) m := by
    intro b p hpm
    change ∑ k ∈ Finset.range (p.degree + 1), _ ∈ _
    refine sum_mem fun k _ => ?_
    by_cases h0 : MvPowerSeries.coeff p (hb b ^ k) = 0
    · rw [h0, zero_div]
      exact zero_mem _
    · have hk : k ≤ rowDegZ' p b := by
        refine le_weight_of_coeff_pow (fun p => rowDegZ' p b)
          (fun a c => by simp [rowDegZ', Finset.sum_add_distrib]) ?_ k p h0
        intro r hr
        rw [hbc] at hr
        split_ifs at hr with h
        · change 1 ≤ rowDegZ' r b
          rw [← degR_eq_row h]
          exact H.2.1 r hr
        · exact absurd rfl hr
      have := hZ' p hpm b
      rw [div_eq_mul_inv]
      refine mul_mem (pow_mem (hint b) k p hpm) (inv_mem_intRing hp _ fun hd => ?_)
      have := hl.dvd_factorial.1 hd
      omega
  rw [hdec, mvExp_sum _ _ hb0]
  exact prod_mem (fun b _ => hexp b) m le_rfl

theorem ubMplus : UBMplus := by
  intro C _ _ v l hl h5 hvl hp n n0 y hn hy h1 H
  exact ubUnit C v l hl h5 hvl hp n n0 y hn hy h1 (constantCoeff_eq_zero H)
    (ubIntegral C v l hl h5 hvl hp n0 y (by omega) h1 H)

theorem main : UBIntegral ∧ UBUnit ∧ UBMplus := ⟨ubIntegral, ubUnit, ubMplus⟩

end GlobalTheory.UnitCase
