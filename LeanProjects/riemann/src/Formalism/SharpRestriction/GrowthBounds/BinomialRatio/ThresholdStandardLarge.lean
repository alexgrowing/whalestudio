import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountLow

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

def pairSet {s : ℕ} (r A : ℕ) (Ai Ci : Fin s → ℕ) :
    Set ((Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) × (Fin r → ℤ)) :=
  {x | IsPair A Ai Ci x.1 x.2}

theorem pairSet_finite (hCD : ChainDimAt) {s : ℕ} (r A : ℕ) (Ai Ci : Fin s → ℕ) : (pairSet r A Ai Ci).Finite := by
  classical
  have hc := chains_finite (r := r) hCD (kLetters A Ai Ci)
  have hl : (⋃ mu ∈ {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ | IsChain (kLetters A Ai Ci) mu},
      Set.Icc (fun i : Fin r => mu (Fin.last _) i.succ) (fun i : Fin r => mu (Fin.last _) i.castSucc)).Finite :=
    hc.biUnion fun mu _ => Set.finite_Icc _ _
  refine (hc.prod hl).subset ?_
  intro t ht
  refine ⟨ht.1, ?_⟩
  simp only [Set.mem_iUnion]
  exact ⟨t.1, ht.1, fun i => (ht.2 i).1, fun i => (ht.2 i).2⟩

theorem tl_symDim_nat (m g : ℕ) : symDim (m + 1) (g : ℤ) = sd m g := by
  unfold symDim sd
  rw [if_neg (by omega)]
  simp

open Classical in

theorem pair_sum (hCD : ChainDimAt) (hNB : NumBranchAt) {s : ℕ} (r A : ℕ) (Ai Ci : Fin s → ℕ) :
    ∑ x ∈ (pairSet_finite hCD r A Ai Ci).toFinset, wdim x.2 = (dimMM (r + 1) (A : ℤ) Ai Ci : ℚ) := by
  have e0 : ∑ x ∈ (pairSet_finite hCD r A Ai Ci).toFinset, wdim x.2 =
      ∑ᶠ x : (Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) × (Fin r → ℤ), if IsPair A Ai Ci x.1 x.2 then wdim x.2 else 0 := by
    rw [finsum_eq_sum_of_support_subset (s := (pairSet_finite hCD r A Ai Ci).toFinset)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      have : IsPair A Ai Ci x.1 x.2 := by simpa [pairSet] using hx
      rw [if_pos this]
    · intro x hx
      by_contra hn
      apply hx
      have : ¬ IsPair A Ai Ci x.1 x.2 := by simpa [pairSet] using hn
      show (if IsPair A Ai Ci x.1 x.2 then wdim x.2 else 0) = 0
      rw [if_neg this]
  have hfin : (support fun x : (Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) × (Fin r → ℤ) =>
      if IsPair A Ai Ci x.1 x.2 then wdim x.2 else 0).Finite := by
    refine (pairSet_finite hCD r A Ai Ci).subset fun x hx => ?_
    by_contra hn
    apply hx
    have : ¬ IsPair A Ai Ci x.1 x.2 := hn
    show (if IsPair A Ai Ci x.1 x.2 then wdim x.2 else 0) = 0
    rw [if_neg this]
  rw [e0, finsum_curry _ hfin]
  have e1 : (dimMM (r + 1) (A : ℤ) Ai Ci : ℚ) = ∏ a, (sdXi (r + 1) ((kLetters A Ai Ci).deg a) : ℚ) := by
    rw [prod_kLetters]
    unfold dimMM
    simp only [tl_symDim_nat]
    push_cast
    rfl
  rw [e1, ← hCD (2 * s + 1) (r + 1) (kLetters A Ai Ci)]
  unfold chainSum
  refine finsum_congr fun mu => ?_
  by_cases hmu : IsChain (kLetters A Ai Ci) mu
  · rw [if_pos ⟨hmu, fun k => k.elim0⟩, hNB r _ (IsChain.anti_last hmu)]
    refine finsum_congr fun lam => ?_
    by_cases hl : Inter (mu (Fin.last _)) lam
    · have hl' : ∀ i : Fin r, mu (Fin.last _) i.succ ≤ lam i ∧ lam i ≤ mu (Fin.last _) i.castSucc := hl
      rw [if_pos hl', if_pos (show IsPair A Ai Ci mu lam from ⟨hmu, hl⟩)]
    · have hl' : ¬ ∀ i : Fin r, mu (Fin.last _) i.succ ≤ lam i ∧ lam i ≤ mu (Fin.last _) i.castSucc := hl
      rw [if_neg hl', if_neg (show ¬ IsPair A Ai Ci mu lam from fun h => hl h.2)]
  · rw [if_neg (fun h => hmu h.1)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro lam
    rw [if_neg (show ¬ IsPair A Ai Ci mu lam from fun h => hmu h.1)]

open Classical in
theorem kept_sum (hCD : ChainDimAt) (p : ℕ) (La : ℝ) {s : ℕ} (r : ℕ) [NeZero r] (A : ℕ) (Ai Ci : Fin s → ℕ) :
    keptPairSum p La (r := r) A Ai Ci =
      ∑ x ∈ (pairSet_finite hCD r A Ai Ci).toFinset, if KeptPair p La Ai Ci x.1 x.2 then wdim x.2 else 0 := by
  unfold keptPairSum
  rw [finsum_eq_sum_of_support_subset (s := (pairSet_finite hCD r A Ai Ci).toFinset)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have : IsPair A Ai Ci x.1 x.2 := by simpa [pairSet] using hx
    by_cases hk : KeptPair p La Ai Ci x.1 x.2
    · rw [if_pos ⟨this, hk⟩, if_pos hk]
    · rw [if_neg (fun h => hk h.2), if_neg hk]
  · intro x hx
    by_contra hn
    apply hx
    have : ¬ IsPair A Ai Ci x.1 x.2 := by simpa [pairSet] using hn
    show (if IsPair A Ai Ci x.1 x.2 ∧ KeptPair p La Ai Ci x.1 x.2 then wdim x.2 else 0) = 0
    rw [if_neg (fun h => this h.1)]

open Classical in

theorem tail_core (hCD : ChainDimAt) (hNB : NumBranchAt) (p : ℕ) (La : ℝ) {s : ℕ} (r : ℕ) [NeZero r] (A : ℕ)
    (Ai Ci : Fin s → ℕ) (Np W e : ℝ) (hW : 0 ≤ W)
    (hN : ((pairSet r A Ai Ci).ncard : ℝ) ≤ Np)
    (hwt : ∀ (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (lam : Fin r → ℤ),
      IsPair A Ai Ci mu lam → ¬ KeptPair p La Ai Ci mu lam →
      ((wdim lam : ℚ) : ℝ) ≤ W * (dimMM (r + 1) (A : ℤ) Ai Ci : ℝ))
    (he : Np * W ≤ e) :
    (1 - e) * (dimMM (r + 1) (A : ℤ) Ai Ci : ℝ) ≤ ((keptPairSum p La (r := r) A Ai Ci : ℚ) : ℝ) := by
  set F := (pairSet_finite hCD r A Ai Ci).toFinset with hF
  set M : ℝ := (dimMM (r + 1) (A : ℤ) Ai Ci : ℝ) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have h1 : (∑ x ∈ F, ((wdim x.2 : ℚ) : ℝ)) = M := by
    have := pair_sum hCD hNB r A Ai Ci
    have h2 : ((∑ x ∈ F, wdim x.2 : ℚ) : ℝ) = ((dimMM (r + 1) (A : ℤ) Ai Ci : ℚ) : ℝ) := by rw [hF, this]
    push_cast at h2
    exact h2
  have h2 : ((keptPairSum p La (r := r) A Ai Ci : ℚ) : ℝ) =
      ∑ x ∈ F, if KeptPair p La Ai Ci x.1 x.2 then ((wdim x.2 : ℚ) : ℝ) else 0 := by
    rw [kept_sum hCD]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  have h3 : ∀ x ∈ F, ((wdim x.2 : ℚ) : ℝ) - W * M ≤ if KeptPair p La Ai Ci x.1 x.2 then ((wdim x.2 : ℚ) : ℝ) else 0 := by
    intro x hx
    have hp : IsPair A Ai Ci x.1 x.2 := by simpa [hF, pairSet] using hx
    have hWM : 0 ≤ W * M := mul_nonneg hW hM0
    split_ifs with hk
    · linarith
    · have := hwt x.1 x.2 hp hk
      linarith
  have h4 := Finset.sum_le_sum h3
  rw [Finset.sum_sub_distrib, h1, Finset.sum_const, nsmul_eq_mul, ← h2] at h4
  have h5 : (F.card : ℝ) ≤ Np := by
    rw [hF, ← Set.ncard_eq_toFinset_card _ (pairSet_finite hCD r A Ai Ci)]
    exact hN
  have h6 : (F.card : ℝ) * (W * M) ≤ e * M := by
    have : (F.card : ℝ) * W ≤ e := le_trans (mul_le_mul_of_nonneg_right h5 hW) he
    calc (F.card : ℝ) * (W * M) = ((F.card : ℝ) * W) * M := by ring
      _ ≤ e * M := mul_le_mul_of_nonneg_right this hM0
  linarith

theorem tail_num (a k C0 : ℝ) (N1 : ℕ) (ha : 9 ≤ a) (hk0 : 0 ≤ k) (hk : k ≤ a) (hN : 1 ≤ N1) (hC : 880 ≤ C0)
    (hL : 1 ≤ Real.log a) :
    (8 * a) ^ (4 * (N1 + 1) ^ 2) *
        (Real.exp (2 - C0 * (N1 : ℝ) ^ 2 * Real.log a / 5) * (8 * a + k) ^ ((2 * N1 + 2) ^ 2)) ≤
      Real.exp (-(C0 * (N1 : ℝ) ^ 2 * Real.log a) / 8) := by
  set L := Real.log a with hLdef
  have ha0 : 0 < a := by linarith
  have hE : Real.exp (2 * L) = a ^ 2 := by
    rw [two_mul, Real.exp_add, hLdef, Real.exp_log ha0]; ring
  have hE1 : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  have hb1 : 8 * a ≤ Real.exp (2 * L) := by rw [hE]; nlinarith
  have hb2 : 8 * a + k ≤ Real.exp (2 * L) := by rw [hE]; nlinarith
  have hn1 : 4 * (N1 + 1) ^ 2 ≤ 16 * N1 ^ 2 := by nlinarith
  have hn2 : (2 * N1 + 2) ^ 2 ≤ 16 * N1 ^ 2 := by nlinarith
  have p1 : (8 * a) ^ (4 * (N1 + 1) ^ 2) ≤ Real.exp (((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L)) := by
    rw [Real.exp_nat_mul]
    exact le_trans (pow_le_pow_left₀ (by linarith) hb1 _) (pow_le_pow_right₀ hE1 hn1)
  have p2 : (8 * a + k) ^ ((2 * N1 + 2) ^ 2) ≤ Real.exp (((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L)) := by
    rw [Real.exp_nat_mul]
    exact le_trans (pow_le_pow_left₀ (by linarith) hb2 _) (pow_le_pow_right₀ hE1 hn2)
  have hN1 : (1 : ℝ) ≤ (N1 : ℝ) := by exact_mod_cast hN
  have hNL : 1 ≤ (N1 : ℝ) ^ 2 * L := by nlinarith [mul_self_nonneg ((N1 : ℝ) - 1)]
  calc (8 * a) ^ (4 * (N1 + 1) ^ 2) *
        (Real.exp (2 - C0 * (N1 : ℝ) ^ 2 * L / 5) * (8 * a + k) ^ ((2 * N1 + 2) ^ 2))
      ≤ Real.exp (((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L)) *
        (Real.exp (2 - C0 * (N1 : ℝ) ^ 2 * L / 5) * Real.exp (((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L))) := by
        apply mul_le_mul p1 _ (by positivity) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left p2 (Real.exp_pos _).le
    _ = Real.exp (((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L) + (2 - C0 * (N1 : ℝ) ^ 2 * L / 5 +
          ((16 * N1 ^ 2 : ℕ) : ℝ) * (2 * L))) := by rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (-(C0 * (N1 : ℝ) ^ 2 * L) / 8) := by
        apply Real.exp_le_exp.mpr
        push_cast
        have : 880 * ((N1 : ℝ) ^ 2 * L) ≤ C0 * ((N1 : ℝ) ^ 2 * L) :=
          mul_le_mul_of_nonneg_right hC (by linarith)
        nlinarith

def PairCountAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        ((pairSet X.m A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry)).ncard : ℝ) ≤
          (8 * (X.a : ℝ)) ^ (4 * (X.N1 + 1) ^ 2)

def NotKeptWtAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        ∀ mu lam, IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          ¬ KeptPair X.p (X.La C0) (r := X.m) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          ((wdim lam : ℚ) : ℝ) ≤ Real.exp (2 - X.La C0 / 5) * (8 * (X.a : ℝ) + X.k) ^ ((2 * X.N1 + 2) ^ 2) *
            (dimMM (X.m + 1) (A : ℤ) (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) : ℝ)

def RestPairCount : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => PairCountAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def RestNotKeptWt : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => NotKeptWtAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem threshold_standard_large : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => 880 ≤ C0 ∧
    ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
  TransportedAlt.of_explicit (fun _ => 880) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 h880 h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      ⟨h880, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩

theorem tail_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hCD : ChainDimAt) (hNB : NumBranchAt) (h880 : 880 ≤ C0)
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X)
    (hP : PairCountAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hW : NotKeptWtAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    TailAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j rz ry hd A hA1 hA2
  have S := hstd X hD hI hc
  have hk5 := S.k5
  have hkQ := S.kQ le_rfl
  have hQ1 := S.Q1
  have hkb := S.kb
  have hb1 : 1 ≤ X.b' := by nlinarith [pow_pos (show (0 : ℝ) < X.k by linarith) 3, pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hk5 3]
  have hka : X.k ≤ X.a := le_trans (le_mul_of_one_le_right (by linarith) hb1) hkb
  have hb9 : 9 ≤ X.b' := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hk5 3]
  have ha9 : (9 : ℝ) ≤ X.a := le_trans hb9 S.ba
  have hnum := tail_num X.a X.k C0 X.N1 ha9 (by linarith) hka S.N1pos h880 S.loga
  have hLa : X.La C0 = C0 * (X.N1 : ℝ) ^ 2 * Real.log X.a := rfl
  refine tail_core hCD hNB X.p (X.La C0) X.m A _ _ ((8 * (X.a : ℝ)) ^ (4 * (X.N1 + 1) ^ 2))
    (Real.exp (2 - X.La C0 / 5) * (8 * (X.a : ℝ) + X.k) ^ ((2 * X.N1 + 2) ^ 2)) _ (by positivity)
    (hP X hD hI hc j rz ry hd A hA1 hA2) (hW X hD hI hc j rz ry hd A hA1 hA2) ?_
  rw [hLa]
  exact hnum

theorem restTail_of (hCD : ChainDimAt) (hNB : NumBranchAt) (hP : RestPairCount) (hW : RestNotKeptWt) : RestTail := by
  refine TransportedAlt.mono ?_ ((threshold_standard_large.and hP).and hW)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨h880, hstd⟩, hp⟩, hw⟩
  exact tail_of hCD hNB h880 hstd hp hw

end Formalism.MainNotions.ColumnSystems.Pf
