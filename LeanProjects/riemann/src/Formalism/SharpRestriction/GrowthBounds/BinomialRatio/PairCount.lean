import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdStandardLarge
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem pc_strip_le {r : ℕ} {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) (i : Fin r) : nu i ≤ mu i + g := by
  have hsum : ∑ j, (nu j - mu j) = (g : ℤ) := by
    rw [Finset.sum_sub_distrib]
    exact h.2.2
  have hle : nu i - mu i ≤ ∑ j, (nu j - mu j) :=
    Finset.single_le_sum (f := fun j => nu j - mu j) (fun j _ => sub_nonneg.2 (h.1 j)) (Finset.mem_univ i)
  linarith

def pcU (n : ℕ) : ℕ := if n = 0 then 0 else n / 2 + 1

def pcL (n : ℕ) : ℕ := (n - 1) / 2

theorem pcU_vec {n : ℕ} (h : n = 0 ∨ n % 2 = 1) : pcU (n + 1) = pcU n + 1 := by
  unfold pcU
  split_ifs <;> omega
theorem pcU_cov {n : ℕ} (h : ¬ (n = 0 ∨ n % 2 = 1)) : pcU (n + 1) = pcU n := by
  unfold pcU
  split_ifs <;> omega
theorem pcL_vec {n : ℕ} (h : n = 0 ∨ n % 2 = 1) : pcL (n + 1) = pcL n := by
  unfold pcL
  omega
theorem pcL_cov {n : ℕ} (h : ¬ (n = 0 ∨ n % 2 = 1)) : pcL (n + 1) = pcL n + 1 := by
  unfold pcL
  omega

theorem pc_deg {s : ℕ} {A : ℕ} {Ai Ci : Fin s → ℕ} {M : ℕ} (hA : ∀ i, Ai i ≤ M) (hC : ∀ i, Ci i ≤ M)
    (a : Fin (2 * s + 1)) : (kLetters A Ai Ci).deg a ≤ if a.val = 0 then A else M := by
  simp only [kLetters]
  split_ifs <;> first | exact le_rfl | exact hA _ | exact hC _ | exact Nat.zero_le _

theorem pc_shape {s r : ℕ} {A : ℕ} {Ai Ci : Fin s → ℕ} {M : ℕ} (hA : ∀ i, Ai i ≤ M) (hC : ∀ i, Ci i ≤ M)
    {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} (h : IsChain (kLetters A Ai Ci) mu) (n : Fin (2 * s + 1 + 1)) :
    ∀ idx : Fin (r + 1), (pcU n.val ≤ idx.val → mu n idx ≤ 0) ∧ (idx.val + pcL n.val < r + 1 → 0 ≤ mu n idx) ∧
      |mu n idx| ≤ (if n.val = 0 then 0 else (A : ℤ)) + n.val * M := by
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg _
  have key : ∀ t : ℕ, ∀ ht : t < 2 * s + 1 + 1, ∀ idx : Fin (r + 1),
      (pcU t ≤ idx.val → mu ⟨t, ht⟩ idx ≤ 0) ∧ (idx.val + pcL t < r + 1 → 0 ≤ mu ⟨t, ht⟩ idx) ∧
      |mu ⟨t, ht⟩ idx| ≤ (if t = 0 then 0 else (A : ℤ)) + (t : ℤ) * M := by
    intro t
    induction t with
    | zero =>
      intro ht idx
      have h0 : mu ⟨0, ht⟩ idx = 0 := by
        rw [show (⟨0, ht⟩ : Fin (2 * s + 1 + 1)) = 0 from rfl, h.1]
        rfl
      refine ⟨fun _ => h0.le, fun _ => h0.ge, ?_⟩
      rw [h0]
      simp
    | succ t ih =>
      intro ht idx
      have ht' : t < 2 * s + 1 + 1 := by omega
      have hlet := h.2 ⟨t, by omega⟩
      have hsucc : (⟨t, by omega⟩ : Fin (2 * s + 1)).succ = ⟨t + 1, ht⟩ := rfl
      have hcast : (⟨t, by omega⟩ : Fin (2 * s + 1)).castSucc = ⟨t, ht'⟩ := rfl
      rw [hsucc, hcast] at hlet
      have hdeg := pc_deg (A := A) hA hC (⟨t, by omega⟩ : Fin (2 * s + 1))
      have hdegZ : ((kLetters A Ai Ci).deg ⟨t, by omega⟩ : ℤ) ≤ (if t = 0 then (A : ℤ) else M) := by
        simp only at hdeg
        split_ifs at hdeg ⊢ <;> exact_mod_cast hdeg
      have hdeg0 : (0 : ℤ) ≤ ((kLetters A Ai Ci).deg ⟨t, by omega⟩ : ℤ) := Int.natCast_nonneg _
      have hB : (if t = 0 then 0 else (A : ℤ)) + (t : ℤ) * M + (if t = 0 then (A : ℤ) else M) ≤
          (if t + 1 = 0 then 0 else (A : ℤ)) + ((t + 1 : ℕ) : ℤ) * M := by
        rcases Nat.eq_zero_or_pos t with rfl | htpos
        · norm_num <;> linarith
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          push_cast
          nlinarith
      by_cases hv : t = 0 ∨ t % 2 = 1
      · have hvec : (kLetters A Ai Ci).vec ⟨t, by omega⟩ = true := by simp [kLetters, hv]
        rw [if_pos hvec] at hlet
        have hsl := pc_strip_le hlet idx
        obtain ⟨hle, hint, _⟩ := hlet
        refine ⟨fun hi => ?_, fun hi => ?_, ?_⟩
        · rw [pcU_vec hv] at hi
          have hi1 : 1 ≤ idx.val := by omega
          have h1 := hint ⟨idx.val - 1, by omega⟩ idx (by show idx.val - 1 + 1 = idx.val; omega)
          have h2 := (ih ht' ⟨idx.val - 1, by omega⟩).1 (by show pcU t ≤ idx.val - 1; omega)
          linarith
        · rw [pcL_vec hv] at hi
          have h1 := (ih ht' idx).2.1 hi
          have h2 := hle idx
          linarith
        · have h1 := (ih ht' idx).2.2
          have h2 := hle idx
          rw [abs_le] at h1 ⊢
          constructor <;> linarith [h1.1, h1.2]
      · have hvec : (kLetters A Ai Ci).vec ⟨t, by omega⟩ = false := by
          simp only [kLetters, decide_eq_false_iff_not]
          exact hv
        rw [if_neg (by rw [hvec]; decide)] at hlet
        have hsl := pc_strip_le hlet idx
        obtain ⟨hle, hint, _⟩ := hlet
        refine ⟨fun hi => ?_, fun hi => ?_, ?_⟩
        · rw [pcU_cov hv] at hi
          have h1 := (ih ht' idx).1 hi
          have h2 := hle idx
          linarith
        · rw [pcL_cov hv] at hi
          have h1 := hint idx ⟨idx.val + 1, by omega⟩ (by show idx.val + 1 = idx.val + 1; rfl)
          have h2 := (ih ht' ⟨idx.val + 1, by omega⟩).2.1 (by show idx.val + 1 + pcL t < r + 1; omega)
          linarith
        · have h1 := (ih ht' idx).2.2
          have h2 := hle idx
          rw [abs_le] at h1 ⊢
          constructor <;> linarith [h1.1, h1.2]
  exact key n.val n.2

def pcPosition (K s q : ℕ) : ℕ := if q < s + 1 then q else K - (2 * s + 1 - q)

def pcEnc (K s : ℕ) (v : Fin K → ℤ) (q : Fin (2 * s + 1)) : ℤ :=
  if h : pcPosition K s q.val < K then v ⟨_, h⟩ else 0

theorem pcEnc_apply {K s : ℕ} (v : Fin K → ℤ) (q : Fin (2 * s + 1)) (i : Fin K) (hs : pcPosition K s q.val = i.val) :
    pcEnc K s v q = v i := by
  unfold pcEnc
  rw [dif_pos (by rw [hs]; exact i.2)]
  congr 1
  exact Fin.ext hs

theorem pcEnc_inj {K s : ℕ} {v v' : Fin K → ℤ} (hz : ∀ i : Fin K, s + 1 ≤ i.val → i.val + s < K → v i = 0)
    (hz' : ∀ i : Fin K, s + 1 ≤ i.val → i.val + s < K → v' i = 0) (he : pcEnc K s v = pcEnc K s v') : v = v' := by
  funext i
  by_cases hzone : s + 1 ≤ i.val ∧ i.val + s < K
  · rw [hz i hzone.1 hzone.2, hz' i hzone.1 hzone.2]
  · have hq : ∃ q : Fin (2 * s + 1), pcPosition K s q.val = i.val := by
      by_cases hi : i.val < s + 1
      · exact ⟨⟨i.val, by omega⟩, by simp [pcPosition, hi]⟩
      · refine ⟨⟨2 * s + 1 - (K - i.val), by have := i.2; omega⟩, ?_⟩
        have h1 : ¬ (2 * s + 1 - (K - i.val) < s + 1) := by have := i.2; omega
        simp only [pcPosition, h1, if_false]
        have := i.2
        omega
    obtain ⟨q, hq⟩ := hq
    have e1 := pcEnc_apply v q i hq
    have e2 := pcEnc_apply v' q i hq
    rw [← e1, ← e2, he]

theorem pcEnc_abs {K s : ℕ} {v : Fin K → ℤ} {T : ℤ} (hT : 0 ≤ T) (hv : ∀ i, |v i| ≤ T) (q : Fin (2 * s + 1)) :
    pcEnc K s v q ∈ Finset.Icc (-T) T := by
  unfold pcEnc
  split_ifs with h
  · exact Finset.mem_Icc.2 (abs_le.1 (hv _))
  · exact Finset.mem_Icc.2 ⟨by linarith, hT⟩

theorem pc_count {s r : ℕ} {A : ℕ} {Ai Ci : Fin s → ℕ} {M : ℕ} (hA : ∀ i, Ai i ≤ M) (hC : ∀ i, Ci i ≤ M) :
    (pairSet r A Ai Ci).ncard ≤ (2 * (A + (2 * s + 1) * M) + 1) ^ ((2 * s + 3) * (2 * s + 1)) := by
  classical
  set T : ℤ := (A : ℤ) + (2 * (s : ℤ) + 1) * M with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hbd : ∀ {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ}, IsChain (kLetters A Ai Ci) mu → ∀ n idx, |mu n idx| ≤ T := by
    intro mu h n idx
    refine (pc_shape hA hC h n idx).2.2.trans ?_
    have hn : (n.val : ℤ) ≤ 2 * (s : ℤ) + 1 := by have := n.2; omega
    have hM : (0 : ℤ) ≤ (M : ℤ) := Int.natCast_nonneg _
    have hA0 : (0 : ℤ) ≤ (A : ℤ) := Int.natCast_nonneg _
    have := mul_le_mul_of_nonneg_right hn hM
    split_ifs <;> linarith
  have hzero : ∀ {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ}, IsChain (kLetters A Ai Ci) mu → ∀ n (i : Fin (r + 1)),
      s + 1 ≤ i.val → i.val + s < r + 1 → mu n i = 0 := by
    intro mu h n i h1 h2
    have hn := n.2
    have hsh := pc_shape hA hC h n i
    have hU : pcU n.val ≤ i.val := by unfold pcU; split_ifs <;> omega
    have hL : i.val + pcL n.val < r + 1 := by unfold pcL; omega
    exact le_antisymm (hsh.1 hU) (hsh.2.1 hL)
  let tgt : Finset ((Fin (2 * s + 1 + 1) → Fin (2 * s + 1) → ℤ) × (Fin (2 * s + 1) → ℤ)) :=
    (Fintype.piFinset fun _ => Fintype.piFinset fun _ => Finset.Icc (-T) T) ×ˢ
      (Fintype.piFinset fun _ => Finset.Icc (-T) T)
  have hlamb : ∀ x ∈ pairSet r A Ai Ci, ∀ i, |x.2 i| ≤ T := by
    intro x hx i
    have h1 := abs_le.mp (hbd hx.1 (Fin.last _) i.succ)
    have h2 := abs_le.mp (hbd hx.1 (Fin.last _) i.castSucc)
    have h3 := hx.2 i
    exact abs_le.mpr ⟨by linarith [h1.1, h3.1], by linarith [h2.2, h3.2]⟩
  have hlamz : ∀ x ∈ pairSet r A Ai Ci, ∀ i : Fin r, s + 1 ≤ i.val → i.val + s < r → x.2 i = 0 := by
    intro x hx i h1 h2
    have h3 := hx.2 i
    have hsh1 := pc_shape hA hC hx.1 (Fin.last _) i.castSucc
    have hsh2 := pc_shape hA hC hx.1 (Fin.last _) i.succ
    have hl : (Fin.last (2 * s + 1)).val = 2 * s + 1 := rfl
    have hU : pcU (Fin.last (2 * s + 1)).val ≤ (i.castSucc : Fin (r + 1)).val := by
      rw [hl]; show pcU (2 * s + 1) ≤ i.val; unfold pcU; split_ifs <;> omega
    have hL : (i.succ : Fin (r + 1)).val + pcL (Fin.last (2 * s + 1)).val < r + 1 := by
      rw [hl, Fin.val_succ]; unfold pcL; omega
    exact le_antisymm (h3.2.trans (hsh1.1 hU)) ((hsh2.2.1 hL).trans h3.1)
  have hle := Set.ncard_le_ncard_of_injOn (s := pairSet r A Ai Ci) (t := (tgt : Set _))
    (fun x => (fun n => pcEnc (r + 1) s (x.1 n), pcEnc r s x.2))
    (by
      intro x hx
      simp only [tgt, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Fintype.mem_piFinset]
      exact ⟨fun n q => pcEnc_abs hT0 (hbd hx.1 n) q, fun q => pcEnc_abs hT0 (hlamb x hx) q⟩)
    (by
      intro x hx y hy hxy
      simp only [Prod.mk.injEq] at hxy
      refine Prod.ext ?_ ?_
      · funext n
        exact pcEnc_inj (hzero hx.1 n) (hzero hy.1 n) (congrFun hxy.1 n)
      · exact pcEnc_inj (hlamz x hx) (hlamz y hy) hxy.2)
    (Finset.finite_toSet tgt)
  rw [Set.ncard_coe_finset] at hle
  refine hle.trans (le_of_eq ?_)
  have hc : (Finset.Icc (-T) T).card = 2 * (A + (2 * s + 1) * M) + 1 := by
    rw [Int.card_Icc]
    have : T + 1 - -T = ((2 * (A + (2 * s + 1) * M) + 1 : ℕ) : ℤ) := by rw [hTdef]; push_cast; ring
    rw [this, Int.toNat_natCast]
  simp only [tgt, Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hc]
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

theorem pc_coarseC_mul {s r : ℕ} (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) (i : Fin s) :
    (coarseC p S aTop b i : ℝ) * (p : ℝ) ^ (S.G - S.d i) ≤ (aTop i : ℝ) := by
  unfold coarseC SegData.P
  have h1 : (aTop i - ∑ c, b.ry i c) / p ^ (S.G - S.d i) * p ^ (S.G - S.d i) ≤ aTop i :=
    (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  exact_mod_cast h1

theorem pairCount_of_std {C0 Cde CE1 CE2 H : ℝ} {X : Loc} (h : Std C0 Cde CE1 CE2 H X) (j : Fin (numSeg X.TT))
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) (A : ℕ) (hA : (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ)) :
    ((pairSet X.m A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry)).ncard : ℝ) ≤
      (8 * (X.a : ℝ)) ^ (4 * (X.N1 + 1) ^ 2) := by
  have hp1 : (1 : ℝ) ≤ X.p := h.p1
  have hp0 : (0 : ℝ) < X.p := by linarith
  have hN1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast h.N1pos
  have hk5 : 5 ≤ X.k := by have := h.N1k; linarith
  have hY := h.Y1
  have hY2 : 1 ≤ X.Y ^ 2 := one_le_pow₀ hY
  have hpk : X.k ^ 2 ≤ X.p := le_trans (by nlinarith [sq_nonneg X.k]) h.pk
  have hb := h.bpos
  have hpb : (X.p : ℝ) * X.b' < X.a := (lt_div_iff₀ hb).mp h.pab
  have hba : X.b' ≤ X.a := by nlinarith
  have hapos : (0 : ℝ) < X.a := by linarith
  have ha1 : (1 : ℝ) ≤ X.a := by
    have : 0 < X.a := by exact_mod_cast hapos
    exact_mod_cast this
  have hbe1 : be X C0 ≤ 1 := by
    have h1 := h.beLe
    have h2 := h.de6
    have h3 : 0 ≤ 18 * (X.N1 : ℝ) * X.La C0 / X.k := by
      have := h.La1
      positivity
    linarith
  have hPp : ∀ i : Fin (segS X.TT j), (X.p : ℝ) ≤
      (X.p : ℝ) ^ ((X.seg C0 CE1 CE2 j).G - (X.seg C0 CE1 CE2 j).d i) := fun i => by
    have hd := dist_pos_lt X.TT j i
    exact le_self_pow₀ hp1 (by show segG X.TT j - (segDists X.TT j).get i ≠ 0; omega)
  set M : ℕ := ⌊2 * (X.a : ℝ) / X.p⌋₊ with hM
  have hAi : ∀ i, clA C0 CE1 CE2 X j rz ry i ≤ M := fun i => by
    apply Nat.le_floor
    rw [le_div_iff₀ hp0]
    have h1 := coarseA_mul X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i
    have h2 : ((X.seg C0 CE1 CE2 j).bTop i : ℝ) ≤ X.b' * (1 + be X C0) := (h.winB _ (pos_mem X.TT j i).1).2
    have h3 : (0 : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i : ℝ) := Nat.cast_nonneg _
    have h4 := mul_le_mul_of_nonneg_left (hPp i) h3
    have h5 : X.b' * (1 + be X C0) ≤ 2 * X.b' := by nlinarith
    show (coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i : ℝ) * X.p ≤ 2 * X.a
    linarith
  have hCi : ∀ i, clC C0 CE1 CE2 X j rz ry i ≤ M := fun i => by
    apply Nat.le_floor
    rw [le_div_iff₀ hp0]
    have h1 := pc_coarseC_mul X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i
    have h2 : ((segATop X.TT X.aT j i : ℕ) : ℝ) ≤ X.a * (1 + 2 / (X.k * X.Y)) := (h.winA _ (pos_mem X.TT j i).1).2
    have h3 : (0 : ℝ) ≤ (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i : ℝ) :=
      Nat.cast_nonneg _
    have h4 := mul_le_mul_of_nonneg_left (hPp i) h3
    have h6 : 2 / (X.k * X.Y) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    have h5 : (X.a : ℝ) * (1 + 2 / (X.k * X.Y)) ≤ 2 * X.a := by nlinarith
    show (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i : ℝ) * X.p ≤ 2 * X.a
    linarith
  have hcount := pc_count (r := X.m) (A := A) hAi hCi
  have hs : segS X.TT j ≤ X.N1 := (h.segB j).2
  have hsr : ((segS X.TT j : ℕ) : ℝ) ≤ X.N1 := by exact_mod_cast hs
  have hMr : (M : ℝ) ≤ 2 * (X.a : ℝ) / X.p := Nat.floor_le (by positivity)
  have hAa : (A : ℝ) ≤ X.a := by
    have h1 := base_exponent_le_a X.p (by have := h.p5; omega) (X.seg C0 CE1 CE2 j) h.E0nn
    have h2 : ((X.seg C0 CE1 CE2 j).a : ℝ) / (X.p : ℝ) ^ (X.seg C0 CE1 CE2 j).G ≤ X.a :=
      div_le_self hapos.le (one_le_pow₀ hp1)
    linarith
  have hsM : (2 * ((segS X.TT j : ℕ) : ℝ) + 1) * (M : ℝ) ≤ X.a := by
    have h1 : 2 * ((segS X.TT j : ℕ) : ℝ) + 1 ≤ X.k := by have := h.N1k; linarith
    have h2 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
    have h3 : (2 * ((segS X.TT j : ℕ) : ℝ) + 1) * (M : ℝ) ≤ X.k * (2 * (X.a : ℝ) / X.p) :=
      mul_le_mul h1 hMr h2 (by linarith)
    have h4 : X.k * (2 * (X.a : ℝ) / X.p) ≤ X.a := by
      rw [mul_div_assoc', div_le_iff₀ hp0]
      have hp2k : 2 * X.k ≤ X.p := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hp2k hapos.le]
    linarith
  have hc : ((2 * (A + (2 * segS X.TT j + 1) * M) + 1 : ℕ) : ℝ) ≤ 8 * (X.a : ℝ) := by
    push_cast
    linarith
  have he : (2 * segS X.TT j + 3) * (2 * segS X.TT j + 1) ≤ 4 * (X.N1 + 1) ^ 2 := by nlinarith
  calc ((pairSet X.m A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry)).ncard : ℝ)
      ≤ (((2 * (A + (2 * segS X.TT j + 1) * M) + 1) ^ ((2 * segS X.TT j + 3) * (2 * segS X.TT j + 1)) : ℕ) : ℝ) := by
        exact_mod_cast hcount
    _ = ((2 * (A + (2 * segS X.TT j + 1) * M) + 1 : ℕ) : ℝ) ^ ((2 * segS X.TT j + 3) * (2 * segS X.TT j + 1)) := by
        push_cast; ring
    _ ≤ (8 * (X.a : ℝ)) ^ ((2 * segS X.TT j + 3) * (2 * segS X.TT j + 1)) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hc _
    _ ≤ (8 * (X.a : ℝ)) ^ (4 * (X.N1 + 1) ^ 2) := pow_le_pow_right₀ (by linarith) he

theorem restPairCount : RestPairCount :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => by
      intro X _ hD hI hc j rz ry _ A _ hA
      exact pairCount_of_std (std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc) j rz ry A hA

end Formalism.MainNotions.ColumnSystems.Pf
