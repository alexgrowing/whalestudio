import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.RootExistence

section Bound

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private def Bd (c : ValueGroupWithZero E) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ i j, valuation E (M i j) ≤ c

variable {a b c : ValueGroupWithZero E} {M N : Matrix (Fin n) (Fin n) E}

private theorem Bd.mono (h : Bd a M) (hab : a ≤ b) : Bd b M := fun i j => (h i j).trans hab

private theorem Bd.zero : Bd a (0 : Matrix (Fin n) (Fin n) E) := fun i j => by simp

private theorem Bd.add (h : Bd a M) (h' : Bd a N) : Bd a (M + N) := fun i j =>
  Valuation.map_add_le _ (h i j) (h' i j)

private theorem Bd.sub (h : Bd a M) (h' : Bd a N) : Bd a (M - N) := fun i j =>
  Valuation.map_sub_le _ (h i j) (h' i j)

private theorem Bd.mul (h : Bd a M) (h' : Bd b N) : Bd (a * b) (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

private theorem Bd.smul (h : Bd a M) (x : E) : Bd (valuation E x * a) (x • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_mul' le_rfl (h i j)

private theorem Bd.nsmul (h : Bd a M) (m : ℕ) : Bd a (m • M) := by
  induction m with
  | zero => simpa using Bd.zero
  | succ m ih => rw [succ_nsmul]; exact ih.add h

private theorem Bd.one : Bd 1 (1 : Matrix (Fin n) (Fin n) E) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs <;> simp

private theorem Bd.of_sub_one (h : Bd a (M - 1)) (ha : a ≤ 1) : Bd 1 M := by
  simpa using (h.mono ha).add Bd.one

private theorem Bd.pow_sub_one (h : Bd a (M - 1)) (ha : a ≤ 1) (m : ℕ) : Bd a (M ^ m - 1) := by
  induction m with
  | zero => simpa using Bd.zero
  | succ m ih =>
    have e : M ^ (m + 1) - 1 = (M ^ m - 1) * M + (M - 1) := by
      rw [pow_succ]; noncomm_ring
    rw [e]
    exact Bd.add (by simpa using ih.mul (h.of_sub_one ha)) h

private theorem Bd.pow_sub_pow (hM : Bd a (M - 1)) (hN : Bd a (N - 1)) (ha : a ≤ 1) (hd : Bd b (M - N)) (m : ℕ) :
    Bd (a * b) (M ^ m - N ^ m - m • (M - N)) := by
  induction m with
  | zero => simpa using Bd.zero
  | succ m ih =>
    have e : M ^ (m + 1) - N ^ (m + 1) - (m + 1) • (M - N) =
        M * (M ^ m - N ^ m - m • (M - N)) + (M - 1) * (m • (M - N)) + (M - N) * (N ^ m - 1) := by
      rw [pow_succ', pow_succ', succ_nsmul]
      generalize m • (M - N) = D
      noncomm_ring
    rw [e]
    refine Bd.add (Bd.add ?_ (hM.mul (hd.nsmul m))) ?_
    · simpa using (hM.of_sub_one ha).mul ih
    · rw [mul_comm a b]
      exact hd.mul (hN.pow_sub_one ha m)

private theorem val_nat_le_one (q : ℕ) : valuation E (q : E) ≤ 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by simp)

end Bound

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem eq_zero_of_bd {ρ c : ValueGroupWithZero E} (hρ : ρ < 1) {M : Matrix (Fin n) (Fin n) E}
    (h : ∀ k : ℕ, Bd (ρ ^ k * c) M) : M = 0 := by
  ext i j
  by_contra hne
  have hv : valuation E (M i j) ≠ 0 := by simpa using hne
  have hc : c ≠ 0 := by
    rintro rfl
    exact hv (by simpa using h 0 i j)
  haveI : MulArchimedean (ValueGroupWithZero E) := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨k, hk⟩ := exists_pow_lt₀ hρ (Units.mk0 (valuation E (M i j) / c) (div_ne_zero hv hc))
  rw [Units.val_mk0, lt_div_iff₀ (zero_lt_iff.mpr hc)] at hk
  exact absurd (h k i j) (not_le.mpr hk)

private theorem isCompact_bd (c : ValueGroupWithZero E) : IsCompact {M : Matrix (Fin n) (Fin n) E | Bd c M} := by
  have h := isCompact_pi_infinite (s := fun _ : Fin n => {x : Fin n → E | ∀ j, x j ∈ {y | valuation E y ≤ c}})
    fun _ => isCompact_pi_infinite fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E c
  exact h

private theorem exists_root (q : ℕ) (r : ValueGroupWithZero E) (hr : r < valuation E (q : E))
    (g : Matrix (Fin n) (Fin n) E) (hg : Bd (r * valuation E (q : E)) (g - 1)) :
    ∃ u : Matrix (Fin n) (Fin n) E, Bd r (u - 1) ∧ u ^ q = g := by
  have hq0 : 0 < valuation E (q : E) := lt_of_le_of_lt zero_le hr
  have hq : (q : E) ≠ 0 := by
    intro h
    simp [h] at hq0
  have hr1 : r ≤ 1 := hr.le.trans (val_nat_le_one q)
  haveI : T2Space E := by
    letI := IsTopologicalAddGroup.rightUniformSpace E
    haveI := isUniformAddGroup_of_addCommGroup (G := E)
    infer_instance
  set ρ := r / valuation E (q : E) with hρ
  have hρ1 : ρ < 1 := (div_lt_one₀ hq0).mpr hr
  let S : ℕ → Set (Matrix (Fin n) (Fin n) E) := fun k =>
    {X | Bd r X} ∩ {X | Bd (ρ ^ k * (r * valuation E (q : E))) ((X + 1) ^ q - g)}
  have hcl : ∀ k, IsClosed (S k) := fun k =>
    (isCompact_bd r).isClosed.inter
      ((isCompact_bd (ρ ^ k * (r * valuation E (q : E)))).isClosed.preimage
        (f := fun X : Matrix (Fin n) (Fin n) E => (X + 1) ^ q - g) (by fun_prop))
  have hanti : ∀ k, S (k + 1) ⊆ S k := fun k X hX =>
    ⟨hX.1, Bd.mono hX.2 (mul_le_mul' (pow_le_pow_right_of_le_one' hρ1.le k.le_succ) le_rfl)⟩
  have hne : ∀ k, (S k).Nonempty := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, Bd.zero, ?_⟩
      have := (Bd.zero (n := n)).sub hg
      simpa using this
    | succ k ih =>
      obtain ⟨X, hX, hX'⟩ := ih
      have hD : Bd (ρ ^ k * r) ((q : E)⁻¹ • ((X + 1) ^ q - g)) := by
        have h := Bd.smul hX' (q : E)⁻¹
        rwa [map_inv₀, ← mul_assoc (ρ ^ k), mul_comm (ρ ^ k * r), inv_mul_cancel_left₀ hq0.ne'] at h
      set D := (q : E)⁻¹ • ((X + 1) ^ q - g) with hDdef
      have hqD : q • D = (X + 1) ^ q - g := by
        rw [hDdef, ← Nat.cast_smul_eq_nsmul E, smul_inv_smul₀ hq]
      have hXD : Bd r (X - D) :=
        Bd.sub hX (hD.mono (by simpa using mul_le_mul' (pow_le_one' hρ1.le k) (le_refl r)))
      refine ⟨X - D, hXD, ?_⟩
      have h := Bd.pow_sub_pow (M := X + 1) (N := X - D + 1) (a := r) (b := ρ ^ k * r)
        (by simpa using hX) (by simpa using hXD) hr1 (by simpa using hD) q
      have e1 : X + 1 - (X - D + 1) = D := by abel
      rw [e1, hqD] at h
      have h' := (Bd.zero (n := n)).sub h
      have e2 : 0 - ((X + 1) ^ q - (X - D + 1) ^ q - ((X + 1) ^ q - g)) = (X - D + 1) ^ q - g := by abel
      have e3 : r * (ρ ^ k * r) = ρ ^ (k + 1) * (r * valuation E (q : E)) := by
        have : ρ * valuation E (q : E) = r := div_mul_cancel₀ _ hq0.ne'
        calc r * (ρ ^ k * r) = ρ * valuation E (q : E) * (ρ ^ k * r) := by rw [this]
          _ = _ := by rw [pow_succ]; ac_rfl
      rw [e2, e3] at h'
      exact h'
  obtain ⟨X, hX⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne
    ((isCompact_bd r).of_isClosed_subset (hcl 0) Set.inter_subset_left) hcl
  rw [Set.mem_iInter] at hX
  exact ⟨X + 1, by simpa using (hX 0).1, sub_eq_zero.mp (eq_zero_of_bd hρ1 fun k => (hX k).2)⟩

private theorem root_unique (q : ℕ) (r : ValueGroupWithZero E) (hr : r < valuation E (q : E))
    {A C : Matrix (Fin n) (Fin n) E} (hA : Bd r (A - 1)) (hC : Bd r (C - 1)) (h : A ^ q = C ^ q) : A = C := by
  have hq0 : 0 < valuation E (q : E) := lt_of_le_of_lt zero_le hr
  have hq : (q : E) ≠ 0 := by
    intro h
    simp [h] at hq0
  have hr1 : r ≤ 1 := hr.le.trans (val_nat_le_one q)
  have hρ1 : r / valuation E (q : E) < 1 := (div_lt_one₀ hq0).mpr hr
  refine sub_eq_zero.mp (eq_zero_of_bd (c := r) hρ1 fun k => ?_)
  induction k with
  | zero => simpa using hA.sub hC
  | succ k ih =>
    have h1 := Bd.pow_sub_pow hA hC hr1 ih q
    rw [h, sub_self] at h1
    have h2 := ((Bd.zero (n := n)).sub h1).smul (q : E)⁻¹
    rw [zero_sub, zero_sub, neg_neg, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hq, map_inv₀] at h2
    refine h2.mono (le_of_eq ?_)
    rw [pow_succ, div_eq_mul_inv]
    ac_rfl

end UpperTheory.ConvolutionTheory.Loc.RootExistence

open UpperTheory.ConvolutionTheory.Loc.RootExistence in
theorem UpperTheory.ConvolutionTheory.Loc.rootEx :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (q : ℕ) (r : ValueGroupWithZero E), r < valuation E (q : E) →
      ∀ g ∈ ball n (r * valuation E (q : E)), ∃! u, u ∈ ball n r ∧ u ^ q = g := by
  intro E _ _ _ _ n q r hr g hg
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hr
  obtain ⟨u, hu, huq⟩ := exists_root q r hr (g : Matrix (Fin n) (Fin n) E) hg
  have hunit : IsUnit u := (isUnit_pow_iff hq).mp (huq ▸ g.isUnit)
  obtain ⟨w, rfl⟩ := hunit
  refine ⟨w, ⟨hu, Units.ext (by simpa using huq)⟩, fun w' hw' => Units.ext ?_⟩
  refine root_unique q r hr hw'.1 hu ?_
  rw [huq, ← hw'.2, Units.val_pow_eq_pow_val]
