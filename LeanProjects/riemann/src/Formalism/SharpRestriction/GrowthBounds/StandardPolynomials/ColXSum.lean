import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColsS
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXCnt
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColXSeg

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.ColumnSystems.Pf.Col

section General

variable {N K : ℕ}

theorem abs_le_colT (ka : Fin (N + 1) → Fin K → ℤ) (i : Fin (N + 1)) (a : Fin K) :
    |ka i a| ≤ ∑ i, ∑ m, |ka i m| :=
  le_trans (Finset.single_le_sum (f := fun m => |ka i m|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))
    (Finset.single_le_sum (f := fun i => ∑ m, |ka i m|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_univ i))

theorem mem_colRange_iff (ka : Fin (N + 1) → Fin K → ℤ) (c : ℤ) :
    c ∈ colRange ka ↔ -(∑ i, ∑ m, |ka i m|) ≤ c ∧ c ≤ ∑ i, ∑ m, |ka i m| := by
  unfold colRange
  exact Finset.mem_Icc

theorem mem_colRange_of (ka : Fin (N + 1) → Fin K → ℤ) (i i' : Fin (N + 1)) (a : Fin K) (c : ℤ)
    (h1 : ka i a < c) (h2 : c ≤ ka i' a) : c ∈ colRange ka := by
  rw [mem_colRange_iff]
  have e1 := abs_le.1 (abs_le_colT ka i a)
  have e2 := abs_le.1 (abs_le_colT ka i' a)
  constructor <;> omega

variable {vecc : Fin N → Bool} {B : Fin N → ℕ} {ka : Fin (N + 1) → Fin K → ℤ} {nu : ℕ → ℤ}

theorem change_count (h : PH vecc B ka nu) (S : Finset ℤ) (hS : colRange ka ⊆ S) (i : Fin N) :
    (S.filter fun c => colH (ka i.castSucc) c ≠ colH (ka i.succ) c).card = B i := by
  have hs := h.kastep i
  by_cases hv : vecc i = true
  · rw [if_pos hv] at hs
    exact strip_count _ _ _ hs S fun a c h1 h2 => hS (mem_colRange_of ka _ _ a c h1 h2)
  · rw [if_neg hv] at hs
    rw [← strip_count _ _ _ hs S fun a c h1 h2 => hS (mem_colRange_of ka _ _ a c h1 h2)]
    congr 1
    exact Finset.filter_congr fun c _ => ne_comm

theorem oc_sum (h : PH vecc B ka nu) (S : Finset ℤ) (hS : colRange ka ⊆ S) (om : Fin (N + 1) → ℕ) :
    ∑ c ∈ S, oc om (muP nu ka) c = ∑ i : Fin N, om i.succ * (if vecc i then B i else 0) := by
  rw [Finset.sum_congr rfl fun c _ => h.oc_eq om c, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hv : vecc i = true
  · rw [if_pos hv, ← change_count h S hS i, Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have := (h.stepV i hv c).1
    by_cases hlt : colH (ka i.castSucc) c < colH (ka i.succ) c
    · rw [if_pos hlt, if_pos (by omega), mul_one]
    · rw [if_neg hlt, if_neg (by omega), mul_zero]
  · rw [if_neg hv, mul_zero]
    refine Finset.sum_eq_zero fun c _ => ?_
    have := (h.stepC i (by simpa using hv) c).1
    rw [if_neg (by omega)]

theorem pl_sum {σ : Type*} (nu : ℕ → ℤ) (h0 : 0 ≤ nu 0) (hm : ∀ t, nu t ≤ nu (t + 1)) (n : ℕ) (S : Finset ℤ)
    (hS : Finset.Icc 1 (nu n) ⊆ S) (v : Fin n → σ) (P : Fin n → ℕ) :
    ∑ c ∈ S, ∑ t : Fin n, (if nu t.val < c ∧ c ≤ nu (t.val + 1) then Finsupp.single (v t) (P t) else 0) =
      ∑ t : Fin n, Finsupp.single (v t) (P t * (nu (t.val + 1) - nu t.val).toNat) := by
  classical
  have mono : Monotone nu := monotone_nat_of_le_succ hm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const]
  have e : S.filter (fun c => nu t.val < c ∧ c ≤ nu (t.val + 1)) = Finset.Ioc (nu t.val) (nu (t.val + 1)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨fun x => x.2, fun x => ⟨hS (Finset.mem_Icc.2 ⟨?_, ?_⟩), x⟩⟩
    · have := mono (Nat.zero_le t.val)
      omega
    · exact le_trans x.2 (mono t.2)
  rw [e, Int.card_Ioc, Finsupp.smul_single, smul_eq_mul, mul_comm]

theorem colH_above (ka : Fin (N + 1) → Fin K → ℤ) (c : ℤ) (hc : ∑ i, ∑ m, |ka i m| < c) (i : Fin (N + 1)) :
    colH (ka i) c = 0 := by
  unfold colH
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ hle
  have := (abs_le.1 (abs_le_colT ka i m)).2
  omega

theorem Kcol_above (R : Type) [CommRing R] (ka : Fin (N + 1) → Fin K → ℤ) (c : ℤ) (hc : ∑ i, ∑ m, |ka i m| < c)
    (t : ℕ) : Kcol R ka c t = extOne := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Kcol]
    split_ifs with h
    · rw [colH_above ka c hc, colH_above ka c hc, ih]
      unfold colStep
      rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
    · exact ih

theorem Psi_eq_prod (R : Type) [CommRing R] (ka : Fin (N + 1) → Fin K → ℤ) (I : ℤ → Finset (Fin K))
    (hI : ∀ c, c ∉ colRange ka → I c = ∅) (M : ℤ) :
    ∏ c ∈ colRange ka ∪ Finset.Icc 1 M, Kcol R ka c N (I c) = Psi R ka I := by
  unfold Psi
  symm
  refine Finset.prod_subset Finset.subset_union_left fun c hc hn => ?_
  rw [hI c hn]
  have h1 : 1 ≤ c := by
    rcases Finset.mem_union.1 hc with h | h
    · exact absurd h hn
    · exact (Finset.mem_Icc.1 h).1
  have h2 : ∑ i, ∑ m, |ka i m| < c := by
    rw [mem_colRange_iff] at hn
    have h3 : (0 : ℤ) ≤ ∑ i, ∑ m, |ka i m| := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ => abs_nonneg _
    by_contra h4
    exact hn ⟨by omega, by omega⟩
  rw [Kcol_above R ka c h2]
  simp [extOne]

end General

section Seg

variable (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT))

theorem PS_even (l : Fin (segS X.TT j)) :
    PS X j (⟨2 * l.val, by have := l.2; omega⟩ : Fin (2 * segS X.TT j + 1)).succ = (X.seg C0 CE1 CE2 j).P X.p l := by
  unfold PS
  rw [posS_succ_lt X j _ (by have := l.2; simp only; omega)]
  show _ = X.p ^ (segG X.TT j - (segDists X.TT j).get l)
  have e2 : (⟨(2 * l.val) / 2, by have := l.2; omega⟩ : Fin (segS X.TT j)) = l := by
    apply Fin.ext; simp
  simp only [e2]
  congr 1
  unfold zS
  omega

theorem PS_last : PS X j (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)).succ = 1 := by
  unfold PS
  rw [posS_succ_ge X j _ (by simp)]
  unfold zS
  simp

theorem nuS_zero : nuS C0 CE1 CE2 mu X β j 0 = 0 := by
  unfold nuS
  rw [if_pos rfl]

theorem nuS_one : nuS C0 CE1 CE2 mu X β j (0 + 1) = a0Z C0 CE1 CE2 mu X β j := by
  unfold nuS
  rw [if_neg (by omega), Finset.sum_eq_zero fun l _ => if_neg (by omega), add_zero]

theorem nuS_step (l : Fin (segS X.TT j)) :
    nuS C0 CE1 CE2 mu X β j (2 * l.val + 1 + 1) = nuS C0 CE1 CE2 mu X β j (2 * l.val + 1) + zxS C0 CE1 CE2 X β j l := by
  unfold nuS
  rw [if_neg (by omega), if_neg (by omega), add_assoc (a0Z C0 CE1 CE2 mu X β j)]
  congr 1
  have e : ∀ l' : Fin (segS X.TT j), (if 2 * (l' : ℕ) + 2 ≤ 2 * l.val + 1 + 1 then (zxS C0 CE1 CE2 X β j l' : ℤ) else 0) =
      (if 2 * (l' : ℕ) + 2 ≤ 2 * l.val + 1 then (zxS C0 CE1 CE2 X β j l' : ℤ) else 0) +
        (if l' = l then (zxS C0 CE1 CE2 X β j l' : ℤ) else 0) := by
    intro l'
    by_cases e : l' = l
    · subst e
      rw [if_pos (by omega), if_neg (by omega), if_pos rfl, zero_add]
    · have : l'.val ≠ l.val := fun x => e (Fin.ext x)
      rw [if_neg e, add_zero]
      exact if_congr (by omega) rfl rfl
  rw [Finset.sum_congr rfl fun l' _ => e l', Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

theorem nuS_cov (l : ℕ) :
    nuS C0 CE1 CE2 mu X β j (2 * l + 1 + 1 + 1) = nuS C0 CE1 CE2 mu X β j (2 * l + 1 + 1) := by
  unfold nuS
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  exact Finset.sum_congr rfl fun l' _ => if_congr (by omega) rfl rfl

theorem nuS_last :
    nuS C0 CE1 CE2 mu X β j (2 * segS X.TT j + 1 + 1) = nuS C0 CE1 CE2 mu X β j (2 * segS X.TT j + 1) := by
  unfold nuS
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  exact Finset.sum_congr rfl fun l' _ => if_congr (by have := l'.2; omega) rfl rfl

end Seg

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X} (L : LvDat C0 CE1 CE2 mu X β)
  (j : Fin (numSeg X.TT)) (y : Tx X.m (L.LL j))

theorem plSum_seg (h : Col.PH (L.LL j).vec (L.LL j).deg y.1.1.mu (nuS C0 CE1 CE2 mu X β j)) :
    ∑ c ∈ colsS C0 CE1 CE2 mu X β j y.1.1.mu, plS C0 CE1 CE2 mu X β j c =
      Finsupp.single ((topStart X j, true), 0) ((X.seg C0 CE1 CE2 j).Qj X.p * (a0Z C0 CE1 CE2 mu X β j).toNat) +
      ∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, true), 0)
        ((X.seg C0 CE1 CE2 j).P X.p i * zxS C0 CE1 CE2 X β j i) := by
  have hsub : Finset.Icc 1 (nuS C0 CE1 CE2 mu X β j (2 * segS X.TT j + 1 + 1)) ⊆
      colsS C0 CE1 CE2 mu X β j y.1.1.mu := by
    unfold colsS
    exact Finset.subset_union_right
  have e0 := pl_sum (nuS C0 CE1 CE2 mu X β j) (h.nonneg 0) h.numono (2 * segS X.TT j + 1 + 1) _ hsub
    (fun t => phiS X j (t, Fin.castAdd X.m 0)) (PS X j)
  refine Eq.trans e0 ?_
  rw [Fin.sum_univ_succ]
  have t0 : (Finsupp.single (phiS X j ((0 : Fin (2 * segS X.TT j + 1 + 1)), Fin.castAdd X.m 0))
      (PS X j 0 * (nuS C0 CE1 CE2 mu X β j (0 + 1) - nuS C0 CE1 CE2 mu X β j 0).toNat) : MonH X) =
      Finsupp.single ((topStart X j, true), 0)
        ((X.seg C0 CE1 CE2 j).Qj X.p * (a0Z C0 CE1 CE2 mu X β j).toNat) := by
    rw [phiS_zero, nuS_one, nuS_zero, sub_zero]
    congr 2
    exact lev_zero X j C0 CE1 CE2
  have tE : ∀ l : Fin (segS X.TT j),
      (Finsupp.single (phiS X j ((⟨2 * l.val, by have := l.2; omega⟩ : Fin (2 * segS X.TT j + 1)).succ, Fin.castAdd X.m 0))
        (PS X j (⟨2 * l.val, by have := l.2; omega⟩ : Fin (2 * segS X.TT j + 1)).succ *
          (nuS C0 CE1 CE2 mu X β j (2 * l.val + 1 + 1) - nuS C0 CE1 CE2 mu X β j (2 * l.val + 1)).toNat) : MonH X) =
      Finsupp.single ((topOdd X j l, true), 0) ((X.seg C0 CE1 CE2 j).P X.p l * zxS C0 CE1 CE2 X β j l) := by
    intro l
    have e1 : phiS X j ((⟨2 * l.val, by have := l.2; omega⟩ : Fin (2 * segS X.TT j + 1)).succ, Fin.castAdd X.m 0) =
        ((topOdd X j l, true), 0) := phiS_odd X j l
    rw [e1, PS_even C0 CE1 CE2, nuS_step, add_sub_cancel_left, Int.toNat_natCast]
  rw [sum_fin_odd]
  refine congrArg₂ (· + ·) t0 ?_
  have tL : (Finsupp.single (phiS X j ((⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)).succ, Fin.castAdd X.m 0))
        (PS X j (⟨2 * segS X.TT j, by omega⟩ : Fin (2 * segS X.TT j + 1)).succ *
          (nuS C0 CE1 CE2 mu X β j (2 * segS X.TT j + 1 + 1) - nuS C0 CE1 CE2 mu X β j (2 * segS X.TT j + 1)).toNat) :
        MonH X) = 0 := by
    rw [nuS_last, sub_self, Int.toNat_zero, mul_zero, Finsupp.single_zero]
  refine Eq.trans (congrArg₂ (· + ·) (Finset.sum_congr rfl fun l _ => ?_) tL) (add_zero _)
  refine Eq.trans (congrArg₂ (· + ·) (tE l) ?_) (add_zero _)
  show (Finsupp.single _ (_ * (nuS C0 CE1 CE2 mu X β j (2 * l.val + 1 + 1 + 1) -
    nuS C0 CE1 CE2 mu X β j (2 * l.val + 1 + 1)).toNat) : MonH X) = 0
  rw [nuS_cov, sub_self, Int.toNat_zero, mul_zero, Finsupp.single_zero]

theorem oSum_seg (h : Col.PH (L.LL j).vec (L.LL j).deg y.1.1.mu (nuS C0 CE1 CE2 mu X β j)) :
    ∑ c ∈ colsS C0 CE1 CE2 mu X β j y.1.1.mu, oCS C0 CE1 CE2 mu X β j y.1.1.mu c =
      (∑ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i *
        (L.LL j).deg ⟨2 * (i : ℕ), by have := i.2; omega⟩) + (L.LL j).deg ⟨2 * segS X.TT j, by omega⟩ := by
  have hsub : colRange y.1.1.mu ⊆ colsS C0 CE1 CE2 mu X β j y.1.1.mu := by
    unfold colsS
    exact Finset.subset_union_left
  refine Eq.trans (oc_sum h _ hsub (PS X j)) ?_
  rw [sum_fin_odd]
  have v3 : (L.LL j).vec ⟨2 * segS X.TT j, by omega⟩ = true := by
    show decide ((2 * segS X.TT j) % 2 = 0) = true
    simp
  rw [if_pos v3, PS_last, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  have v1 : (L.LL j).vec ⟨2 * l.val, by have := l.2; omega⟩ = true := by
    show decide ((2 * l.val) % 2 = 0) = true
    simp
  have v2 : (L.LL j).vec ⟨2 * l.val + 1, by have := l.2; omega⟩ = false := by
    show decide ((2 * l.val + 1) % 2 = 0) = false
    simp
  rw [if_pos v1, if_neg (by rw [v2]; simp), mul_zero, add_zero, PS_even C0 CE1 CE2]

theorem dKsum_seg (h : Col.PH (L.LL j).vec (L.LL j).deg y.1.1.mu (nuS C0 CE1 CE2 mu X β j))
    (i : Fin (2 * segS X.TT j + 1)) :
    ∑ c ∈ colsS C0 CE1 CE2 mu X β j y.1.1.mu, dKS X j y.1.1.mu c i = (L.LL j).deg i := by
  have hsub : colRange y.1.1.mu ⊆ colsS C0 CE1 CE2 mu X β j y.1.1.mu := by
    unfold colsS
    exact Finset.subset_union_left
  refine Eq.trans ?_ (change_count h _ hsub i)
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold dKS
  by_cases e : colH (y.1.1.mu i.castSucc) c = colH (y.1.1.mu i.succ) c
  · rw [if_pos e, if_neg (not_not.2 e)]
  · rw [if_neg e, if_pos e]

theorem Kprod_seg (R : Type) [CommRing R] :
    ∏ c ∈ colsS C0 CE1 CE2 mu X β j y.1.1.mu, Kcol R y.1.1.mu c (2 * segS X.TT j + 1) (y.1.2 c) =
      psiR R (L.LL j) y := by
  unfold colsS psiR
  exact Psi_eq_prod R y.1.1.mu y.1.2 y.2.1 _

end Formalism.MainNotions.ColumnSystems.Pf.GenusGluing
