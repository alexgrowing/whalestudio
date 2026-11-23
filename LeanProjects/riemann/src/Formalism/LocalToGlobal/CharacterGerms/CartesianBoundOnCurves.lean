import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.ScaledSecondIntegral

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

private theorem exists_subring_iff_ge_zero : ∃ R : Subring C, ∀ a, a ∈ R ↔ V.Ge 0 a := by
  refine ⟨{ carrier := {a | V.Ge 0 a}
            mul_mem' := ?_
            one_mem' := ?_
            add_mem' := ?_
            zero_mem' := ?_
            neg_mem' := ?_ }, fun a => Iff.rfl⟩
  · intro a b ha hb
    have ha' : ((0 : ℝ) : WithTop ℝ) ≤ V.v a := ha
    have hb' : ((0 : ℝ) : WithTop ℝ) ≤ V.v b := hb
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v (a * b)
    rw [AddValuation.map_mul]
    rw [WithTop.coe_zero] at ha' hb' ⊢
    exact add_nonneg ha' hb'
  · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 1
    rw [AddValuation.map_one, WithTop.coe_zero]
  · intro a b ha hb
    have ha' : ((0 : ℝ) : WithTop ℝ) ≤ V.v a := ha
    have hb' : ((0 : ℝ) : WithTop ℝ) ≤ V.v b := hb
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v (a + b)
    exact le_trans (le_min ha' hb') (V.v.map_add a b)
  · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
    rw [AddValuation.map_zero]
    exact le_top
  · intro a ha
    have ha' : ((0 : ℝ) : WithTop ℝ) ≤ V.v a := ha
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v (-a)
    rw [AddValuation.map_neg]
    exact ha'

theorem VF.Ge.prod {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.Ge 0 (∏ i ∈ s, f i) := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  exact (hR _).1 (prod_mem fun i hi => (hR _).2 (h i hi))

theorem det_int (M : Matrix I I C) (h : ∀ i j, V.Ge 0 (M i j)) : V.Ge 0 M.det := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  have hM : M = (Matrix.of fun a b => (⟨M a b, (hR _).2 (h a b)⟩ : R)).map R.subtype := by
    ext a b
    rfl
  rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (hR _).1 (Subtype.mem _)

theorem inv_unit_int {a : C} (h : V.v a = 0) : V.Ge 0 a⁻¹ := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at h
    exact WithTop.top_ne_zero h
  have e : V.v a + V.v a⁻¹ = 0 := by
    rw [← AddValuation.map_mul, mul_inv_cancel₀ ha, AddValuation.map_one]
  rw [h, zero_add] at e
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v a⁻¹
  rw [e, WithTop.coe_zero]

theorem inv_int (M : Matrix I I C) (h : ∀ i j, V.Ge 0 (M i j)) (hd : V.v M.det = 0) :
    ∀ i j, V.Ge 0 (M⁻¹ i j) := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  have hadj : ∀ i j, V.Ge 0 (M.adjugate i j) := by
    have hM : M = (Matrix.of fun a b => (⟨M a b, (hR _).2 (h a b)⟩ : R)).map R.subtype := by
      ext a b
      rfl
    intro i j
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    exact (hR _).1 (Subtype.mem _)
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hR _).1 (mul_mem ((hR _).2 (inv_unit_int hd)) ((hR _).2 (hadj i j)))

namespace Cart

variable (X : Cart V d I J)

def remL (L : (I ⊕ J → C) → ℕ → I ⊕ J → C) (x : ℕ → I ⊕ J → C) : ℕ → (ℕ → I ⊕ J → C)
  | 0 => x
  | s + 1 => remL L x s - Vpow s (L (remL L x s s))

variable {X} {L : (I ⊕ J → C) → ℕ → I ⊕ J → C}

private theorem vpow_mem_Ty (s : ℕ) {y : ℕ → I ⊕ J → C} (hy : y ∈ X.Ty) : Vpow s y ∈ X.Ty := by
  induction s with
  | zero =>
    have e : Vpow 0 y = y := by
      funext i n
      simp [Vpow]
    rw [e]
    exact hy
  | succ s ih =>
    have e : Vpow (s + 1) y = Vpow 1 (Vpow s y) := by
      funext i n
      simp only [Vpow]
      split_ifs <;> first | rfl | omega | rw [show i - (s + 1) = i - 1 - s by omega]
    rw [e]
    exact X.V_mem _ ih

theorem remL_spec (hmem : ∀ h, (∀ n, V.Ge 0 (h n)) → L h ∈ X.Ty) (hzero : ∀ h, L h 0 = h)
    {x : ℕ → I ⊕ J → C} (hx : x ∈ X.Ty) :
    ∀ s, remL L x s ∈ X.Ty ∧ ∀ j < s, remL L x s j = 0 := by
  intro s
  induction s with
  | zero => exact ⟨hx, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ s ih =>
    obtain ⟨hmemS, hz⟩ := ih
    have hint : ∀ n, V.Ge 0 (remL L x s s n) := X.t2 _ hmemS s hz
    have hL := hmem _ hint
    refine ⟨?_, fun j hj => ?_⟩
    · show remL L x s - Vpow s (L (remL L x s s)) ∈ X.Ty
      exact sub_mem hmemS (vpow_mem_Ty s hL)
    · show remL L x s j - Vpow s (L (remL L x s s)) j = 0
      funext n
      simp only [Pi.sub_apply, Vpow]
      rcases (Nat.lt_succ_iff.mp hj).lt_or_eq with hj | rfl
      · rw [if_pos hj, hz j hj]
        simp
      · rw [if_neg (lt_irrefl _), Nat.sub_self, hzero]
        simp

theorem remL_eq (x : ℕ → I ⊕ J → C) (s : ℕ) :
    remL L x s = x - ∑ s' ∈ Finset.range s, Vpow s' (L (remL L x s' s')) := by
  induction s with
  | zero => simp [remL]
  | succ s ih =>
    show remL L x s - Vpow s (L (remL L x s s)) = _
    rw [Finset.sum_range_succ, ← sub_sub, ← ih]

theorem expansionL (hmem : ∀ h, (∀ n, V.Ge 0 (h n)) → L h ∈ X.Ty) (hzero : ∀ h, L h 0 = h)
    {x : ℕ → I ⊕ J → C} (hx : x ∈ X.Ty) :
    ∃ h : ℕ → I ⊕ J → C, (∀ s n, V.Ge 0 (h s n)) ∧ x = sumV (fun s => L (h s)) := by
  refine ⟨fun s => remL L x s s,
    fun s n => X.t2 _ (remL_spec hmem hzero hx s).1 s (remL_spec hmem hzero hx s).2 n, ?_⟩
  funext i n
  have h0 := (remL_spec hmem hzero hx (i + 1)).2 i (Nat.lt_succ_self i)
  rw [remL_eq] at h0
  have h1 := congrFun h0 n
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.zero_apply] at h1
  rw [sub_eq_zero] at h1
  rw [h1]
  simp only [sumV]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [Vpow]
  rw [if_neg (by simp at hs; omega)]

end Cart

namespace Sys

variable {X : Cart V d I J} (S : Sys X)

theorem mem (c : I) : S.cur c ∈ X.Ty := (S.curve c).1

theorem pure (c : I) : ∀ (i : ℕ) n, X.ty n ≠ X.ty (Sum.inl c) + i → S.cur c i n = 0 := (S.curve c).2.2

theorem cur_zero_inl (c k : I) : S.cur c 0 (Sum.inl k) = S.tan c k := by
  rw [(S.curve c).2.1]
  rfl

theorem be_zero (c : I) (κ : J) : S.cur c 0 (Sum.inr κ) = 0 := by
  rw [(S.curve c).2.1]
  rfl

def U : Matrix I I C := Matrix.of S.tan

theorem U_int (c k : I) : V.Ge 0 (S.U c k) := by
  have := X.t2 _ (S.mem c) 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) (Sum.inl k)
  rw [S.cur_zero_inl] at this
  exact this

theorem U_det_ne : S.U.det ≠ 0 := by
  intro h0
  have := S.unimod
  change V.v S.U.det = 0 at this
  rw [h0, AddValuation.map_zero] at this
  exact WithTop.top_ne_zero this

def co (h : I ⊕ J → C) (b : I) : C := ∑ k, h (Sum.inl k) * S.U⁻¹ k b

theorem co_int {h : I ⊕ J → C} (hh : ∀ n, V.Ge 0 (h n)) (b : I) : V.Ge 0 (S.co h b) := by
  obtain ⟨R, hR⟩ := exists_subring_iff_ge_zero (V := V)
  have hinv := inv_int S.U (fun i j => S.U_int i j) S.unimod
  show V.Ge 0 (∑ k, h (Sum.inl k) * S.U⁻¹ k b)
  exact (hR _).1 (sum_mem fun k _ => mul_mem ((hR _).2 (hh _)) ((hR _).2 (hinv k b)))

theorem co_spec (h : I ⊕ J → C) (k : I) : ∑ b, S.co h b * S.U b k = h (Sum.inl k) := by
  have hU : S.U⁻¹ * S.U = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have e : ∀ j, ∑ b, S.U⁻¹ j b * S.U b k = (1 : Matrix I I C) j k := fun j => by
    rw [← hU, Matrix.mul_apply]
  simp only [co, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, e, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

def lift (h : I ⊕ J → C) : ℕ → I ⊕ J → C :=
  (∑ b, teich V.l (S.co h b) (S.cur b)) + const0 (Sum.elim (0 : I → C) (fun j => h (Sum.inr j)))

theorem lift_mem {h : I ⊕ J → C} (hh : ∀ n, V.Ge 0 (h n)) : S.lift h ∈ X.Ty := add_mem (sum_mem fun b _ => X.teich_mem _ (S.co_int hh b) _ (S.mem b)) (X.t3 _ fun j => hh _)

theorem lift_apply (h : I ⊕ J → C) (i : ℕ) (n : I ⊕ J) : S.lift h i n =
    (∑ b, S.co h b ^ (V.l ^ i) * S.cur b i n) +
      const0 (Sum.elim (0 : I → C) (fun j => h (Sum.inr j))) i n := by
  simp only [lift, Pi.add_apply, Finset.sum_apply, teich]

theorem lift_zero (h : I ⊕ J → C) : S.lift h 0 = h := by
  funext n
  rw [lift_apply]
  rcases n with k | κ
  · simp only [pow_zero, pow_one, cur_zero_inl, const0, if_true, Sum.elim_inl, Pi.zero_apply, add_zero]
    exact S.co_spec h k
  · simp only [pow_zero, pow_one, be_zero, mul_zero, Finset.sum_const_zero, const0, if_true,
      Sum.elim_inr, zero_add]

end Sys

private theorem ge_zero_l_pow_mul_of_mem_Ty (X : Cart V d I J) :
    ∀ (i : ℕ) (x : ℕ → I ⊕ J → C), x ∈ X.Ty → ∀ n, V.Ge 0 ((V.l : C) ^ i * x i n) := by
  intro i
  induction i with
  | zero =>
    intro x hx n
    rw [pow_zero, one_mul]
    exact X.t2 x hx 0 (fun j hj => absurd hj (Nat.not_lt_zero _)) n
  | succ i ih =>
    intro x hx n
    have h := ih (Fs V.l x) (X.F_mem x hx) n
    simp only [Fs] at h
    rw [pow_succ, mul_assoc]
    exact h

private theorem ge_neg_of_ge_zero_l_pow_mul (i : ℕ) (y : C) (h : V.Ge 0 ((V.l : C) ^ i * y)) : V.Ge (-(i : ℝ)) y := by
  unfold VF.Ge at *
  rw [AddValuation.map_mul, AddValuation.map_pow, V.v_l] at h
  have hi : (i • (1 : WithTop ℝ)) = ((i : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]
  rw [hi] at h
  by_cases hy : V.v y = ⊤
  · rw [hy]
    exact le_top
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hy
    rw [← ht] at h ⊢
    rw [← WithTop.coe_add] at h
    have h' := WithTop.coe_le_coe.mp h
    exact WithTop.coe_le_coe.mpr (by linarith)

theorem lattice_inclusion_forms_injective (X : Cart V d I J) : LatticeInclusionFormsInjective X := by
  intro S c i n
  exact ge_neg_of_ge_zero_l_pow_mul i _ (ge_zero_l_pow_mul_of_mem_Ty X i _ (S.mem c) n)

private theorem ge_mono' {w w' : ℝ} {a : C} (h : V.Ge w a) (hw : w' ≤ w) : V.Ge w' a :=
  le_trans (WithTop.coe_le_coe.mpr hw) h

theorem eq16 (X : Cart V d I J) : Eq16 X := by
  intro a u x hx i hi
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · obtain rfl : i = 1 := by omega
    refine ⟨fun k => ?_, fun κ => ?_⟩
    · rw [hx.2 k]
      show ((_ : ℝ) : WithTop ℝ) ≤ V.v 0
      rw [AddValuation.map_zero]
      exact le_top
    · exact ge_mono' (hx.bound_one _) (by norm_num)
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    refine ⟨fun k => ge_mono' (hx.bound j _) (by push_cast; linarith),
      fun κ => ge_mono' (hx.bound j _) (by push_cast; linarith [le_max_right (1 : ℝ) ((j : ℝ) + 2 - 1)])⟩

theorem sysExists (X : Cart V d I J) : SysExists X := by
  intro u hu hty hdet
  have hc : ∀ c, ∃ x, X.IsCurve (X.ty (Sum.inl c)) (u c) x := fun c => by
    obtain ⟨x, hx, h0, hp⟩ := X.t4 (X.ty (Sum.inl c)) (u c) (hu c) (fun k hk => hty c k hk)
    exact ⟨x, hx, h0, hp⟩
  choose cur hcur using hc
  exact ⟨⟨u, cur, hcur, hdet⟩, rfl⟩

theorem structEqAll (X : Cart V d I J) : StructEqAll X := by
  intro S
  have hz : V.Ge 0 (0 : C) := by
    show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
    rw [AddValuation.map_zero]
    exact le_top
  have hexp : ∀ a, ∃ h : ℕ → I ⊕ J → C, (∀ s n, V.Ge 0 (h s n)) ∧
      Fs V.l (S.cur a) = sumV (fun s => S.lift (h s)) := fun a =>
    Cart.expansionL (X := X) (L := S.lift) (fun h hh => S.lift_mem hh) (fun h => S.lift_zero h)
      (X.F_mem _ (S.mem a))
  choose H hHint hHeq using hexp
  refine ⟨fun s a b => if X.ty (Sum.inl b) = X.ty (Sum.inl a) + 1 + s then S.co (H a s) b else 0,
    fun i a κ => if X.ty (Sum.inr κ) = X.ty (Sum.inl a) + 1 + i then H a i (Sum.inr κ) else 0,
    ?_, ?_, ?_, ?_⟩
  · intro s a b
    beta_reduce
    split_ifs
    · exact S.co_int (hHint a s) b
    · exact hz
  · intro s a κ
    beta_reduce
    split_ifs
    · exact hHint a s (Sum.inr κ)
    · exact hz
  · intro s a b hb
    beta_reduce
    rw [if_neg hb]
  · intro a i n
    beta_reduce
    have pur : ∀ b (j : ℕ), X.ty n ≠ X.ty (Sum.inl b) + j → S.cur b j n = 0 :=
      fun b j h => S.pure b j n h
    have hl0 : ∀ k : ℕ, ((0 : C) ^ (V.l ^ k)) = 0 := fun k =>
      zero_pow (pow_ne_zero _ V.l_prime.ne_zero)
    by_cases hn : X.ty n = X.ty (Sum.inl a) + 1 + i
    · have e := congrFun (congrFun (hHeq a) i) n
      simp only [Fs, sumV] at e
      rw [e]
      simp only [Sys.lift_apply, Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun b _ => ?_
        have hsi : s ≤ i := by simp at hs; omega
        split_ifs with hb
        · rfl
        · have hc : S.cur b (i - s) n = 0 := pur b (i - s) (by
            intro h'
            apply hb
            rw [Nat.cast_sub hsi, hn] at h'
            linear_combination -h')
          rw [hc, mul_zero, mul_zero]
      · rw [Finset.sum_eq_single i]
        · simp only [Nat.sub_self, const0, ↓reduceIte]
          rcases n with k | κ
          · rfl
          · simp only [Sum.elim_inr]
            rw [if_pos hn]
        · intro s hs hsi
          have hne : i - s ≠ 0 := by simp at hs; omega
          simp only [const0, if_neg hne]
        · intro h
          exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self i)) h
    · have hL : S.cur a (i + 1) n = 0 := pur a (i + 1) (by
        intro h'
        apply hn
        rw [h']
        push_cast
        ring)
      rw [hL, mul_zero]
      symm
      rw [Finset.sum_eq_zero, zero_add]
      · rcases n with k | κ
        · rfl
        · simp only [Sum.elim_inr]
          rw [if_neg hn]
      · intro s hs
        have hsi : s ≤ i := by simp at hs; omega
        refine Finset.sum_eq_zero fun b _ => ?_
        split_ifs with hb
        · have hc : S.cur b (i - s) n = 0 := pur b (i - s) (by
            intro h'
            apply hn
            rw [h', hb, Nat.cast_sub hsi]
            ring)
          rw [hc, mul_zero]
        · rw [hl0, zero_mul]

end Formalism.L2.FormalSeriesBounds
