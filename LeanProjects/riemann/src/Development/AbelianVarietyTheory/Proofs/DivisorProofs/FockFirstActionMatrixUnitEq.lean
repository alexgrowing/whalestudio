import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLineMatrixKroneckerRightFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueJointTop

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm

namespace GlobalTheory.CompactHarm

variable {m k l : ℕ}

def zVar (m k l : ℕ) : Fin k × Fin m → Ix m 0 × Ix k l := fun w => (.inl w.2, .inl w.1)

def yVar' (m k l : ℕ) : Fin l × Fin m → Ix m 0 × Ix k l := fun w => (.inl w.2, .inr w.1.rev)

theorem omE_pp {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = true) (hv : linePos v = true)
    (P : Pol p q r s) :
    omE u v P = X u * pderiv v P + (if u = v then (1 / 2 : ℂ) else 0) • P := by
  simp only [omE, raiB, lowB, hu, hv, if_true]
  split_ifs <;> simp

theorem omE_nn {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = false) (hv : linePos v = false)
    (P : Pol p q r s) :
    omE u v P = -(X v * pderiv u P) - (if u = v then (1 / 2 : ℂ) else 0) • P := by
  have : omE u v P = -(pderiv u (X v * P)) + (if u = v then (1 / 2 : ℂ) else 0) • P := by
    simp only [omE, raiB, lowB, hu, hv, Bool.false_eq_true, if_false]
    split_ifs <;> simp
  rw [this, pderiv_X_mul']
  split_ifs
  · module
  · simp

theorem fockFirstAction_matrixUnit_eq (i j : Fin m) (P : Pol m 0 k l) :
    fockAct1 m 0 k l (Eab (.inl i) (.inl j)) P = mixedOp ℂ (zVar m k l) (yVar' m k l) i j P +
      (if i = j then ((cPair k l : ℚ) : ℂ) else 0) • P := by
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, mixedOp_apply,
    ← Equiv.sum_comp Fin.revPerm (fun d : Fin l => omE _ _ P)]
  simp only [omE_pp (Sum.inl _, Sum.inl _) (Sum.inl _, Sum.inl _) rfl rfl,
    omE_nn (Sum.inl _, Sum.inr _) (Sum.inl _, Sum.inr _) rfl rfl, zVar, yVar',
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Fin.revPerm_apply,
    Prod.mk.injEq, Sum.inl.injEq, and_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    cPair, ← Nat.cast_smul_eq_nsmul ℂ]
  split_ifs
  · push_cast; module
  · simp [sub_eq_add_neg]

theorem fock_action_left_block (c c' : Fin k) (P : Pol m 0 k l) :
    fockAct2 m 0 k l (Eab (.inl c) (.inl c')) P = rowOp ℂ (zVar m k l) c c' P +
      (if c = c' then ((cPair m 0 : ℚ) : ℂ) else 0) • P := by
  rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, rowOp_apply]
  simp only [omE_pp (Sum.inl _, Sum.inl _) (Sum.inl _, Sum.inl _) rfl rfl, zVar,
    Finset.sum_add_distrib, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Prod.mk.injEq, Sum.inl.injEq, true_and, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    cPair, ← Nat.cast_smul_eq_nsmul ℂ]
  split_ifs
  · push_cast; module
  · simp

theorem fock_action_right_block (d d' : Fin l) (P : Pol m 0 k l) :
    fockAct2 m 0 k l (Eab (.inr d.rev) (.inr d'.rev)) P = -rowOp ℂ (yVar' m k l) d' d P -
      (if d = d' then ((cPair m 0 : ℚ) : ℂ) else 0) • P := by
  rw [fockAct2_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, rowOp_apply]
  simp only [omE_nn (Sum.inl _, Sum.inr _) (Sum.inl _, Sum.inr _) rfl rfl, yVar',
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Prod.mk.injEq, Sum.inr.injEq, true_and, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    cPair, ← Nat.cast_smul_eq_nsmul ℂ, Fin.rev_inj]
  split_ifs
  · push_cast; module
  · simp

theorem mem_hwSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧
      ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem mem_harm1_iff (P : Pol m 0 k l) : P ∈ harm1 m 0 k l ↔
    ∀ c d, ∑ i, pderiv (zVar m k l (c, i)) (pderiv (yVar' m k l (d, i)) P) = 0 := by
  have hf := fun Z hZ => ((GlobalTheory.FockParts.explicit_parts m 0 k l).2 Z hZ P).2
  constructor
  · intro h c d
    have hZ : IsPC (Eab (.inr d.rev) (.inl c) : Mat k l) := by
      rintro (a | a) (b | b) hab <;> simp [Eab, sameBlock] at hab ⊢
    have := h _ hZ
    rw [hf _ hZ] at this
    simp [Eab, Matrix.single_apply, ite_and, linePos, Fintype.sum_sum_type] at this
    simpa [zVar, yVar', pderiv_swap (Sum.inl _, Sum.inl _)] using this
  · intro h Z hZ
    rw [hf _ hZ]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    rcases c with c | c
    · simp [linePos, Fintype.sum_sum_type]
    rcases d with d | d
    · have := h d c.rev
      simp only [zVar, yVar', Fin.rev_rev, pderiv_swap (Sum.inl _, Sum.inl _)] at this
      simp [linePos, Fintype.sum_sum_type, ← Finset.smul_sum, this]
    · simp [hZ (.inr c) (.inr d) trivial]

theorem mem_span_harm1_iff (P : Pol m 0 k l) :
    P ∈ Submodule.span ℂ (harm1 m 0 k l) ↔ P ∈ harm1 m 0 k l := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem P hP => exact hP
  | zero => simp [mem_harm1_iff]
  | add P Q _ _ hP hQ =>
    rw [mem_harm1_iff] at *
    intro c d
    simp only [map_add, Finset.sum_add_distrib, hP, hQ, add_zero]
  | smul s P _ hP =>
    rw [mem_harm1_iff] at *
    intro c d
    simp only [Derivation.map_smul, ← Finset.smul_sum, hP, smul_zero]

theorem mem_iff_jointTop (μ : Ix m 0 → ℚ) (μ' : Ix k l → ℚ) (P : Pol m 0 k l) :
    P ∈ hwSub (fockAct1 m 0 k l) μ ⊓ hwSub (fockAct2 m 0 k l) μ' ⊓
      Submodule.span ℂ (harm1 m 0 k l) ↔
    JointTop (zVar m k l) (yVar' m k l) (fun i => (shiftNu (cPair k l) μ (.inl i) : ℚ))
      (fun c => (shiftNu (cPair m 0) μ' (.inl c) : ℚ))
      (fun d => (-shiftNu (cPair m 0) μ' (.inr d.rev) : ℚ)) P := by
  simp only [Submodule.mem_inf, mem_hwSub_iff, mem_span_harm1_iff, mem_harm1_iff, JointTop,
    Sum.forall, posC, IsEmpty.forall_iff, false_imp_iff, implies_true, and_true, true_and,
    fockFirstAction_matrixUnit_eq, fock_action_left_block, if_true, shiftNu]
  have e1 : (∀ a b : Fin m, a < b → mixedOp ℂ (zVar m k l) (yVar' m k l) a b P +
      (if a = b then ((cPair k l : ℚ) : ℂ) else 0) • P = 0) ↔
      ∀ a b : Fin m, a < b → mixedOp ℂ (zVar m k l) (yVar' m k l) a b P = 0 :=
    forall₃_congr fun a b h => by simp [h.ne]
  have e2 : (∀ a b : Fin k, a < b → rowOp ℂ (zVar m k l) a b P +
      (if a = b then ((cPair m 0 : ℚ) : ℂ) else 0) • P = 0) ↔
      ∀ a b : Fin k, a < b → rowOp ℂ (zVar m k l) a b P = 0 :=
    forall₃_congr fun a b h => by simp [h.ne]
  have e3 : (∀ a b : Fin l, a < b → fockAct2 m 0 k l (Eab (.inr a) (.inr b)) P = 0) ↔
      ∀ a b : Fin l, a < b → rowOp ℂ (yVar' m k l) a b P = 0 := by
    constructor
    · intro h a b hab
      have := h _ _ (Fin.rev_lt_rev.2 hab)
      rw [fock_action_right_block] at this
      simpa [hab.ne'] using this
    · intro h a b hab
      rw [← a.rev_rev, ← b.rev_rev, fock_action_right_block, h _ _ (Fin.rev_lt_rev.2 hab)]
      simp [hab.ne]
  have e4 : (∀ a : Fin l, fockAct2 m 0 k l (Eab (.inr a) (.inr a)) P = (μ' (.inr a) : ℂ) • P) ↔
      ∀ a : Fin l, rowOp ℂ (yVar' m k l) a a P =
        ((-(μ' (.inr a.rev) + cPair m 0) : ℚ) : ℂ) • P := by
    rw [← Fin.revPerm.forall_congr_right]
    refine forall_congr' fun a => ?_
    rw [Fin.revPerm_apply, fock_action_right_block, if_pos rfl, sub_eq_iff_eq_add, neg_eq_iff_eq_neg]
    push_cast
    rw [neg_smul, add_smul]
  simp only [e1, e2, e3, e4, Rat.cast_sub, sub_smul, eq_sub_iff_add_eq]
  tauto

theorem getD_pad (x : List ℤ) (n : ℕ) (y : List ℤ) (i : ℕ) :
    (pad x n y).getD i 0 = ((x.getD i 0 +
      if x.length + n ≤ i then y.getD (i - (x.length + n)) 0 else 0 : ℤ) : ℚ) := by
  refine (List.getD_map (x ++ List.replicate n 0 ++ y) (0 : ℤ) (fun v : ℤ => (v : ℚ))).trans ?_
  congr 1
  by_cases h1 : i < x.length
  · rw [List.append_assoc, List.getD_append _ _ _ _ h1, if_neg (by omega), add_zero]
  · rw [List.getD_eq_default x _ (by omega), zero_add]
    split_ifs with h2
    · rw [List.getD_append_right _ _ _ _ (by simpa using h2)]
      simp
    · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega)]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp

theorem pad_values (la lb : List ℤ) (a : Fin k → ℕ) (b : Fin l → ℕ)
    (h : la.length + lb.length ≤ m) (hp : la.length ≤ k) (hq : lb.length ≤ l)
    (ha : ∀ c, (a c : ℤ) = la.getD c 0)
    (hb : ∀ d, (b d : ℤ) = if (d : ℕ) < lb.length then -lb.getD (lb.length - 1 - d) 0 else 0) :
    (∀ i : Fin m, (pad la (m - la.length - lb.length) lb).getD i 0 = mixedWeight m a b i) ∧
    (∀ c : Fin k, (pad la (k - la.length) []).getD c 0 = a c) ∧
    ∀ d : Fin l, (pad [] (l - lb.length) lb).getD d.rev 0 = -(b d : ℚ) := by
  refine ⟨fun i => ?_, fun c => ?_, fun d => ?_⟩
  · rw [getD_pad, mixedWeight_apply, sub_eq_add_neg]
    have := i.2
    congr 2
    · split_ifs with h1
      · rw [ha]
      · exact List.getD_eq_default _ _ (by omega)
    · simp only [hb]
      split_ifs with h1 h2 h3 h2 h3 <;> first | omega | simp
      congr 2
      omega
  · rw [getD_pad, ← ha]; simp
  · rw [getD_pad, ← Int.cast_natCast, hb, ← Int.cast_neg]
    have := d.2
    congr 1
    simp only [List.getD_nil, List.length_nil, zero_add, Fin.val_rev]
    split_ifs with h1 h2 h2 <;> first | omega | simp
    congr 2
    omega

theorem zVar_inj : Function.Injective (zVar m k l) := fun u w e => by
  simpa [zVar, Prod.ext_iff, and_comm] using e

theorem yVar'_inj : Function.Injective (yVar' m k l) := fun u w e => by
  simpa [yVar', Prod.ext_iff, and_comm] using e

theorem zVar_ne (u w) : zVar m k l u ≠ yVar' m k l w := by simp [zVar, yVar']

theorem zVar_or (s : Ix m 0 × Ix k l) : (∃ u, zVar m k l u = s) ∨ ∃ w, yVar' m k l w = s := by
  rcases s with ⟨i | i, c | c⟩
  · exact .inl ⟨(c, i), rfl⟩
  · exact .inr ⟨(c.rev, i), by simp [yVar']⟩
  · exact i.elim0
  · exact i.elim0

theorem sum_abs_mixedWeight {p q : ℕ} (h : p + q ≤ m) (a : Fin p → ℕ) (b : Fin q → ℕ) :
    ∑ i, |mixedWeight m a b i| = ∑ c, (a c : ℤ) + ∑ d, (b d : ℤ) := by
  rw [← sum_dite_lt (show p ≤ m by omega), ← sum_dite_rev_lt (show q ≤ m by omega),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := i.2
  rw [mixedWeight_apply]
  split_ifs <;> first | omega | simp

theorem compact_member_harmonics : ∀ (m k l : ℕ) (μ : Ix m 0 → ℚ) (μ' : Ix k l → ℚ), (JointShape m 0 k l μ μ' → Module.finrank ℂ ↥(hwSub (fockAct1 m 0 k l) μ ⊓ hwSub (fockAct2 m 0 k l) μ' ⊓ Submodule.span ℂ (harm1 m 0 k l)) = 1) ∧ (∀ P ∈ hwSub (fockAct1 m 0 k l) μ ⊓ hwSub (fockAct2 m 0 k l) μ' ⊓ Submodule.span ℂ (harm1 m 0 k l), P ≠ 0 → (∃ d : ℕ, (d : ℚ) = degW (cPair k l) μ ∧ P ∈ homog (Ix m 0 × Ix k l) d) ∧ ∃ a b : List ℤ, (∀ v ∈ a, 0 < v) ∧ (∀ v ∈ b, v < 0) ∧ a.length + b.length ≤ m ∧ a.length ≤ k ∧ b.length ≤ l ∧ shiftNu (cPair k l) μ = ofBlocks (pad a (m - a.length - b.length) b) [] ∧ shiftNu (cPair m 0) μ' = ofBlocks (pad a (k - a.length) []) (pad [] (l - b.length) b)) := by
  intro m k l μ μ'
  constructor
  · rintro ⟨la, lb, lc, ld, ha, -, hb, -, pa, pb, -, -, h1, h2, h3, h4, e1, e2⟩
    obtain rfl : lc = [] := List.length_eq_zero_iff.1 (by omega)
    obtain rfl : ld = [] := List.length_eq_zero_iff.1 (by omega)
    simp only [List.length_nil, add_zero, zero_add, Nat.sub_zero] at h3 h4 e1 e2
    have ha' : ∀ i, 0 ≤ la.getD i 0 := fun i => by
      by_cases hi : i < la.length
      · rw [List.getD_eq_getElem _ _ hi]; exact (ha _ (List.getElem_mem _)).le
      · rw [List.getD_eq_default _ _ (by omega)]
    have hb' : ∀ i, lb.getD i 0 ≤ 0 := fun i => by
      by_cases hi : i < lb.length
      · rw [List.getD_eq_getElem _ _ hi]; exact (hb _ (List.getElem_mem _)).le
      · rw [List.getD_eq_default _ _ (by omega)]
    have mono : ∀ L : List ℤ, L.Pairwise (· ≥ ·) → ∀ i j, i ≤ j → j < L.length →
        L.getD j 0 ≤ L.getD i 0 := fun L hL i j hij hj => by
      rcases hij.eq_or_lt with rfl | hij
      · rfl
      rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (hij.trans hj)]
      exact List.pairwise_iff_getElem.1 hL i j _ _ hij
    obtain ⟨a, hae⟩ : ∃ a : Fin k → ℕ, ∀ c, (a c : ℤ) = la.getD c 0 :=
      ⟨fun c => (la.getD c 0).toNat, fun c => Int.toNat_of_nonneg (ha' c)⟩
    obtain ⟨b, hbe⟩ : ∃ b : Fin l → ℕ, ∀ d, (b d : ℤ) =
        if (d : ℕ) < lb.length then -lb.getD (lb.length - 1 - d) 0 else 0 :=
      ⟨fun d => (if (d : ℕ) < lb.length then -lb.getD (lb.length - 1 - d) 0 else 0).toNat,
        fun d => Int.toNat_of_nonneg (by
          split_ifs
          · exact neg_nonneg.2 (hb' _)
          · rfl)⟩
    obtain ⟨v1, v2, v3⟩ := pad_values la lb a b h1 h3 h4 hae hbe
    obtain ⟨P₀, hP0, hP, hu⟩ := exists_unique_jointTop _ zVar_inj _ yVar'_inj zVar_ne zVar_or
      h1 h3 h4 a b
      (fun i j hij => by
        refine Int.ofNat_le.1 ?_
        rw [hae, hae]
        by_cases hj : (j : ℕ) < la.length
        · exact mono la pa i j hij hj
        · rw [List.getD_eq_default _ _ (by omega)]; exact ha' _)
      (fun i j hij => by
        refine Int.ofNat_le.1 ?_
        have hij' : (i : ℕ) ≤ j := hij
        rw [hbe, hbe]
        split_ifs with g1 g2 g2
        · exact neg_le_neg (mono lb pb _ _ (by omega) (by omega))
        · omega
        · exact neg_nonneg.2 (hb' _)
        · rfl)
      (fun c hc => by
        have := hae c
        rw [List.getD_eq_default _ _ hc] at this
        exact_mod_cast this)
      (fun c hc => by
        have := hbe c
        rw [if_neg (by omega)] at this
        exact_mod_cast this)
    have key : ∀ P, P ∈ hwSub (fockAct1 m 0 k l) μ ⊓ hwSub (fockAct2 m 0 k l) μ' ⊓
        Submodule.span ℂ (harm1 m 0 k l) ↔ JointTop (zVar m k l) (yVar' m k l)
          (fun i => (mixedWeight m a b i : ℂ)) (fun c => a c) (fun d => b d) P := fun P => by
      rw [mem_iff_jointTop, e1, e2]
      simp only [ofBlocks, v1, v2, v3, neg_neg, Rat.cast_intCast, Rat.cast_natCast]
    have : hwSub (fockAct1 m 0 k l) μ ⊓ hwSub (fockAct2 m 0 k l) μ' ⊓
        Submodule.span ℂ (harm1 m 0 k l) = ℂ ∙ P₀ := by
      refine le_antisymm (fun P h => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ((key _).2 hP))
      obtain ⟨r, rfl⟩ := hu P ((key P).1 h)
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    rw [this, finrank_span_singleton hP0]
  · intro P hP hP0
    obtain ⟨a, b, p, q, h, hp, hq, ha, hb, e1, e2, e3, hhom⟩ := weights_of_jointTop _ zVar_inj _
      yVar'_inj zVar_ne zVar_or _ _ _ hP0 ((mem_iff_jointTop μ μ' P).1 hP)
    have ha0 : ∀ c : Fin k, p ≤ c → a c = 0 := fun c hc => by have := ha c; omega
    have hb0 : ∀ c : Fin l, q ≤ c → b c = 0 := fun c hc => by have := hb c; omega
    have f1 : ∀ i, shiftNu (cPair k l) μ (.inl i) = mixedWeight m a b i := fun i => by
      exact_mod_cast congrFun e1 i
    have f2 : ∀ c, shiftNu (cPair m 0) μ' (.inl c) = a c := fun i => by
      exact_mod_cast congrFun e2 i
    have f3 : ∀ d : Fin l, -shiftNu (cPair m 0) μ' (.inr d.rev) = b d := fun i => by
      exact_mod_cast congrFun e3 i
    refine ⟨⟨_, ?_, hhom⟩, ?_⟩
    · have := sum_abs_mixedWeight h (fun c => a (Fin.castLE hp c)) (fun d => b (Fin.castLE hq d))
      rw [mixedWeight_restrict hp hq a b ha0 hb0,
        sum_castLE hp (fun c => (a c : ℤ)) fun c hc => by simp [ha0 c hc],
        sum_castLE hq (fun c => (b c : ℤ)) fun c hc => by simp [hb0 c hc]] at this
      simp only [degW, Fintype.sum_sum_type, f1, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      exact_mod_cast this.symm
    let la : List ℤ := List.ofFn fun c : Fin p => (a (Fin.castLE hp c) : ℤ)
    let lb : List ℤ := List.ofFn fun j : Fin q => -(b (Fin.castLE hq j.rev) : ℤ)
    have lla : la.length = p := List.length_ofFn
    have llb : lb.length = q := List.length_ofFn
    obtain ⟨v1, v2, v3⟩ := pad_values (m := m) la lb a b (by omega) (by omega) (by omega)
      (fun c => by
        by_cases hc : (c : ℕ) < p
        · rw [List.getD_eq_getElem _ _ (by omega)]; simp [la]
        · rw [List.getD_eq_default _ _ (by omega), ha0 c (by omega)]; rfl)
      (fun d => by
        split_ifs with hd
        · rw [List.getD_eq_getElem _ _ (by omega)]
          simp only [lb, List.getElem_ofFn, neg_neg]
          congr 2
          ext
          simp at hd ⊢
          omega
        · rw [hb0 d (by omega)]; rfl)
    refine ⟨la, lb, fun v hv => ?_, fun v hv => ?_, by omega, by omega, by omega, ?_, ?_⟩
    · obtain ⟨c, rfl⟩ := List.mem_ofFn.1 hv
      exact_mod_cast (ha _).2 c.2
    · obtain ⟨c, rfl⟩ := List.mem_ofFn.1 hv
      exact neg_neg_of_pos (by exact_mod_cast (hb _).2 c.rev.2)
    · funext i
      rcases i with i | i
      · rw [f1, ← v1]; rfl
      · exact i.elim0
    · funext c
      rcases c with c | d
      · rw [f2, ← v2]; rfl
      · have g1 := f3 d.rev
        have g2 := v3 d.rev
        rw [Fin.rev_rev] at g1 g2
        rw [← g1, neg_neg] at g2
        exact g2.symm

end GlobalTheory.CompactHarm
