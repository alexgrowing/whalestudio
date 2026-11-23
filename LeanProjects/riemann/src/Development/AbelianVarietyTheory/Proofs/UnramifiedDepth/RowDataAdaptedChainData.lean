import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.LocalToGlobal.CharacterGerms.ScaledSecondIntegral

noncomputable section

open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.AdaptedChain

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

def intRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => ha.mul_int hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => ha.neg

theorem frob_sum {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i, V.Ge 0 (f i)) (k : ℕ) :
    V.Ge 1 ((∑ i ∈ s, f i) ^ (V.l ^ k) - ∑ i ∈ s, f i ^ (V.l ^ k)) := by
  induction s using Finset.induction_on with
  | empty => simpa [zero_pow (pow_pos V.l_prime.pos k).ne'] using VF.Ge.zero 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : V.Ge 0 (∑ i ∈ s, f i) := VF.Ge.sum fun i _ => hf i
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime (⟨f a, hf a⟩ : intRing V) ⟨_, hs⟩ k
    have hr' := congrArg Subtype.val hr
    simp only [Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast] at hr'
    have h1 : V.Ge 1 ((V.l : C) * (f a * (∑ i ∈ s, f i) * (r : C))) := by
      simpa using (((hf a).mul_int hs).mul_int r.2).l_mul
    have := h1.add ih
    convert this using 1
    rw [hr']; ring

theorem int_of_pow {x : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (x ^ n)) : V.Ge 0 x := by
  unfold VF.Ge at h ⊢
  rw [V.v.map_pow] at h
  induction hv : V.v x using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv] at h
    have h' : ((0 : ℝ) : WithTop ℝ) ≤ ((n • t : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_nsmul]; exact h
    have h'' : (0 : ℝ) ≤ n • t := by exact_mod_cast h'
    rw [nsmul_eq_mul] at h''
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have : 0 ≤ t := by by_contra hc; push_neg at hc; nlinarith
    exact_mod_cast this

def admitted (V : VF C) (Q : Finset I) (P : Matrix I I C) : Prop :=
  (∀ c x, V.Ge 0 (P c x)) ∧ V.v P.det = 0 ∧ (∀ c, c ∉ Q → ∀ x, P c x = if x = c then 1 else 0) ∧
    ∀ c ∈ Q, ∀ x, x ∉ Q → P c x = 0

theorem isAdmissibleIntegralBasisChange_one (Q : Finset I) : admitted V Q (1 : Matrix I I C) := by
  refine ⟨fun c x => ?_, by simp, fun c _ x => by simp [Matrix.one_apply, eq_comm], fun c hc x hx => ?_⟩
  · rw [Matrix.one_apply]; split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  · exact Matrix.one_apply_ne (fun h => hx (h ▸ hc))

theorem elim_one (Q : Finset I) (a : I → C) : ∃ (P : Matrix I I C) (Q' : Finset I), admitted V Q P ∧ Q' ⊆ Q ∧
    Q.card ≤ Q'.card + 1 ∧ ∀ c ∈ Q', ∑ x, P c x * a x = 0 := by
  by_cases h0 : ∀ c ∈ Q, a c = 0
  · refine ⟨1, Q, isAdmissibleIntegralBasisChange_one Q, subset_rfl, by omega, fun c hc => ?_⟩
    simp [Matrix.one_apply, h0 c hc]
  push_neg at h0
  obtain ⟨c1, hc1, ha1⟩ := h0
  obtain ⟨c0, hc0, hmin⟩ := Q.exists_min_image (fun c => V.v (a c)) ⟨c1, hc1⟩
  have ha0 : a c0 ≠ 0 := by
    intro h
    have := hmin c1 hc1
    simp only [h, V.v.map_zero, top_le_iff] at this
    exact ha1 (by simpa using this)
  have hint : ∀ c ∈ Q, V.Ge 0 (a c / a c0) := by
    intro c hc
    have h1 := hmin c hc
    have h2 : V.v (a c) = V.v (a c / a c0) + V.v (a c0) := by
      rw [← V.v.map_mul, div_mul_cancel₀ _ ha0]
    have h3 : V.v (a c0) ≠ ⊤ := by simpa using ha0
    rw [h2] at h1
    unfold VF.Ge
    have : (0 : WithTop ℝ) + V.v (a c0) ≤ V.v (a c / a c0) + V.v (a c0) := by simpa using h1
    exact (WithTop.add_le_add_iff_right h3).mp this
  set col : I → C := fun c => if c = c0 then 1 else if c ∈ Q then -(a c / a c0) else 0 with hcol
  refine ⟨Matrix.updateCol 1 c0 col, Q.erase c0, ⟨?_, ?_, ?_, ?_⟩, Finset.erase_subset _ _, ?_, ?_⟩
  · intro c x
    rw [Matrix.updateCol_apply]
    split_ifs with h
    · simp only [hcol]
      split_ifs with h1 h2
      · exact VF.Ge.one
      · exact (hint c h2).neg
      · exact VF.Ge.zero 0
    · exact (isAdmissibleIntegralBasisChange_one Q).1 c x
  · rw [← Matrix.cramer_apply, Matrix.cramer_one]
    simp [hcol]
  · intro c hc x
    have : c ≠ c0 := fun h => hc (h ▸ hc0)
    rw [Matrix.updateCol_apply]
    by_cases h : x = c0
    · subst h; simp [hcol, this, hc, this.symm]
    · simp [h, Matrix.one_apply, eq_comm]
  · intro c hc x hx
    have : x ≠ c0 := fun h => hx (h ▸ hc0)
    rw [Matrix.updateCol_apply, if_neg this]
    exact Matrix.one_apply_ne (fun h => hx (h ▸ hc))
  · rw [Finset.card_erase_of_mem hc0]; omega
  · intro c hc
    obtain ⟨hne, hcQ⟩ := Finset.mem_erase.mp hc
    have : ∀ x, Matrix.updateCol (1 : Matrix I I C) c0 col c x * a x =
        (if x = c0 then -(a c) else 0) + (if x = c then a c else 0) := by
      intro x
      rw [Matrix.updateCol_apply]
      by_cases h : x = c0
      · subst h; simp [hcol, hne, hcQ, hne.symm, ha0]
      · by_cases h' : x = c
        · subst h'; simp [h]
        · simp [h, h', Matrix.one_apply_ne (Ne.symm h')]
    simp only [this, Finset.sum_add_distrib]
    simp

theorem admitted.mul {Q Q' : Finset I} (hQ : Q' ⊆ Q) {P P' : Matrix I I C} (h : admitted V Q P)
    (h' : admitted V Q' P') : admitted V Q (P' * P) := by
  refine ⟨fun c x => ?_, ?_, fun c hc x => ?_, fun c hc x hx => ?_⟩
  · rw [Matrix.mul_apply]; exact VF.Ge.sum fun y _ => (h'.1 _ _).mul_int (h.1 _ _)
  · rw [Matrix.det_mul, V.v.map_mul, h.2.1, h'.2.1, add_zero]
  · rw [Matrix.mul_apply]
    simp only [h'.2.2.1 c (fun hh => hc (hQ hh))]
    simp [h.2.2.1 c hc x]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : y ∈ Q
    · rw [h.2.2.2 y hy x hx, mul_zero]
    · by_cases hc' : c ∈ Q'
      · rw [h'.2.2.2 c hc' y (fun hh => hy (hQ hh)), zero_mul]
      · rw [h'.2.2.1 c hc' y, if_neg (fun hh : y = c => hy (hh ▸ hc)), zero_mul]

theorem elim {M : Type} (Q : Finset I) (a : I → M → C) (E : Finset M) :
    ∃ (P : Matrix I I C) (Q' : Finset I), admitted V Q P ∧ Q' ⊆ Q ∧
    Q.card ≤ Q'.card + E.card ∧ ∀ c ∈ Q', ∀ e ∈ E, ∑ x, P c x * a x e = 0 := by
  induction E using Finset.induction_on with
  | empty => exact ⟨1, Q, isAdmissibleIntegralBasisChange_one Q, subset_rfl, by simp, by simp⟩
  | insert e E he ih =>
    obtain ⟨P, Q1, hP, h1, hc1, hz⟩ := ih
    obtain ⟨P', Q2, hP', h2, hc2, hz'⟩ := elim_one (V := V) Q1 (fun y => ∑ x, P y x * a x e)
    refine ⟨P' * P, Q2, hP.mul h1 hP', h2.trans h1, by rw [Finset.card_insert_of_notMem he]; omega, ?_⟩
    intro c hc e' he'
    have key : ∑ x, (P' * P) c x * a x e' = ∑ y, P' c y * ∑ x, P y x * a x e' := by
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    rw [key]
    rcases Finset.mem_insert.mp he' with rfl | he'
    · exact hz' c hc
    · refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y ∈ Q1
      · rw [hz y hy e' he', mul_zero]
      · rw [hP'.2.2.2 c (h2 hc) y hy, zero_mul]

theorem elim_frob [IsAlgClosed C] {M : Type} (Q : Finset I) (w : I → M → C)
    (hw : ∀ x e, V.Ge 0 (w x e)) (E : Finset M) (k : ℕ) :
    ∃ (P : Matrix I I C) (Q' : Finset I), admitted V Q P ∧ Q' ⊆ Q ∧
    Q.card ≤ Q'.card + E.card ∧ ∀ c ∈ Q', ∀ e ∈ E, V.Ge 1 (∑ x, P c x ^ (V.l ^ k) * w x e) := by
  have hpos : 0 < V.l ^ k := pow_pos V.l_prime.pos k
  choose r hr using fun x e => IsAlgClosed.exists_pow_nat_eq (w x e) hpos
  obtain ⟨P, Q', hP, h1, h2, h3⟩ := elim (V := V) Q r E
  refine ⟨P, Q', hP, h1, h2, fun c hc e he => ?_⟩
  have := (frob_sum (V := V) Finset.univ (fun x => P c x * r x e)
    (fun x => (hP.1 c x).mul_int (int_of_pow hpos.ne' (by rw [hr]; exact hw x e))) k).neg
  rw [h3 c hc e he, zero_pow hpos.ne'] at this
  simpa [mul_pow, hr] using this

theorem exists_unit_minor {ι : Type} [Fintype ι] (U : ι → I → C) (w : I → ι → C)
    (hU : ∀ c x, V.Ge 0 (U c x)) (hw : ∀ x c, V.Ge 0 (w x c))
    (h : ∀ c c', ∑ x, U c x * w x c' = if c = c' then 1 else 0) :
    ∃ f : ι → I, V.v (Matrix.of fun c' c => U c (f c')).det = 0 := by
  by_contra hcon
  push_neg at hcon
  have h1 : (Matrix.of fun c' => ∑ x, w x c' • (fun c => U c x) : Matrix ι ι C) = 1 := by
    ext c' c
    simp only [Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.one_apply]
    rw [show (if c' = c then (1 : C) else 0) = if c = c' then 1 else 0 by simp [eq_comm], ← h]
    simp only [mul_comm]
  have h2 : (1 : C) = ∑ f : ι → I, (∏ c', w (f c') c') * (Matrix.of fun c' c => U c (f c')).det := by
    have e := (Matrix.detRowAlternating (n := ι) (R := C)).toMultilinearMap.map_sum
      (fun c' x => w x c' • (fun c => U c x))
    simp only [MultilinearMap.map_smul_univ, smul_eq_mul] at e
    have e1 : (Matrix.of fun c' => ∑ x, w x c' • (fun c => U c x) : Matrix ι ι C).det = 1 := by
      rw [h1, Matrix.det_one]
    rw [← e1]
    exact e
  have h3 : (0 : WithTop ℝ) < V.v (1 : C) := by
    rw [h2]
    refine V.v.map_lt_sum WithTop.zero_ne_top fun f _ => ?_
    rw [V.v.map_mul]
    have a1 : V.Ge 0 (∏ c', w (f c') c') := VF.Ge.prod fun c _ => hw _ _
    have a2 : V.Ge 0 (Matrix.of fun c' c => U c (f c')).det := det_int _ fun _ _ => hU _ _
    have a3 : (0 : WithTop ℝ) < V.v (Matrix.of fun c' c => U c (f c')).det :=
      lt_of_le_of_ne a2 (hcon f).symm
    exact lt_of_lt_of_le a3 (le_add_of_nonneg_left a1)
  simp at h3

variable {X : Cart V d I J}

theorem tan_eq {S S' : Sys X} {c : I} (h : S'.cur c = S.cur c) : S'.tan c = S.tan c := by
  funext k; rw [← S.cur_zero_inl, ← S'.cur_zero_inl, h]

theorem tan_pure (S : Sys X) {c k : I} (h : X.ty (Sum.inl k) ≠ X.ty (Sum.inl c)) : S.tan c k = 0 := by
  rw [← S.cur_zero_inl]; exact S.pure c 0 _ (by simpa using h)

def Stable (V : VF C) (L : AddSubgroup (I → C)) : Prop := ∀ r, V.Ge 0 r → ∀ u ∈ L, r • u ∈ L

theorem change (S : Sys X) (b : ZMod d) (Q : Finset I) (hQ : ∀ c ∈ Q, X.ty (Sum.inl c) = b)
    (L : AddSubgroup (I → C)) (hL : Stable V L) (hQL : ∀ c ∈ Q, S.tan c ∈ L)
    (P : Matrix I I C) (hP : admitted V Q P) :
    ∃ S' : Sys X, (∀ c, c ∉ Q → S'.cur c = S.cur c) ∧ (∀ c ∈ Q, S'.tan c ∈ L) ∧
      ∀ c i n, S'.cur c i n = ∑ x, P c x ^ (V.l ^ i) * S.cur x i n := by
  have lpos : ∀ k : ℕ, V.l ^ k ≠ 0 := fun k => (pow_pos V.l_prime.pos k).ne'
  have hty : ∀ c x, X.ty (Sum.inl x) ≠ X.ty (Sum.inl c) → P c x = 0 := by
    intro c x h
    by_cases hc : c ∈ Q
    · exact hP.2.2.2 c hc x (fun hx => h (by rw [hQ c hc, hQ x hx]))
    · rw [hP.2.2.1 c hc x, if_neg (fun hh : x = c => h (by rw [hh]))]
  have hval : ∀ c i n, (∑ x, teich V.l (P c x) (S.cur x)) i n = ∑ x, P c x ^ (V.l ^ i) * S.cur x i n := by
    intro c i n; simp [Finset.sum_apply, teich]
  refine ⟨⟨fun c k => (P * S.U) c k, fun c => ∑ x, teich V.l (P c x) (S.cur x), fun c => ⟨?_, ?_, ?_⟩, ?_⟩,
    fun c hc => ?_, fun c hc => ?_, hval⟩
  · exact X.Ty.sum_mem fun x _ => X.teich_mem _ (hP.1 _ _) _ (S.mem x)
  · funext n
    rw [hval]
    cases n with
    | inl k => simp [S.cur_zero_inl, Matrix.mul_apply, Sys.U]
    | inr j => simp [S.be_zero]
  · intro i n hn
    rw [hval]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : X.ty (Sum.inl x) = X.ty (Sum.inl c)
    · rw [S.pure x i n (by rw [hx]; exact hn), mul_zero]
    · rw [hty c x hx, zero_pow (lpos i), zero_mul]
  · show V.v (P * S.U).det = 0
    rw [Matrix.det_mul, V.v.map_mul, hP.2.1, zero_add]
    exact S.unimod
  · funext i n
    show (∑ x, teich V.l (P c x) (S.cur x)) i n = _
    rw [hval]
    simp [hP.2.2.1 c hc, zero_pow (lpos i)]
  · have : (fun k => (P * S.U) c k) = ∑ x, P c x • S.tan x := by
      funext k; simp [Matrix.mul_apply, Sys.U, Finset.sum_apply]
    show (fun k => (P * S.U) c k) ∈ L
    rw [this]
    refine L.sum_mem fun x _ => ?_
    by_cases hx : x ∈ Q
    · exact hL _ (hP.1 _ _) _ (hQL x hx)
    · rw [hP.2.2.2 c hc x hx, zero_smul]; exact L.zero_mem

theorem modify (S : Sys X) (Q : Finset I) (h : ∀ c ∈ Q, ∀ k, V.Ge 0 (S.cur c 1 (Sum.inl k))) :
    ∃ S' : Sys X, (∀ c, c ∉ Q → S'.cur c = S.cur c) ∧ S'.tan = S.tan ∧
      ∀ c ∈ Q, ∀ k, S'.cur c 1 (Sum.inl k) = 0 := by
  have : ∀ c, ∃ y, X.IsCurve (X.ty (Sum.inl c)) (S.tan c) y ∧ (c ∉ Q → y = S.cur c) ∧
      (c ∈ Q → ∀ k, y 1 (Sum.inl k) = 0) := by
    intro c
    by_cases hc : c ∈ Q
    · obtain ⟨z, hz, hz0, hzp⟩ := X.t4 (X.ty (Sum.inl c) + 1) (fun k => S.cur c 1 (Sum.inl k)) (h c hc)
        (fun k hk => S.pure c 1 _ (by simpa using hk))
      refine ⟨S.cur c - Vpow 1 z, ⟨X.Ty.sub_mem (S.mem c) (X.V_mem _ hz), ?_, ?_⟩, fun hh => absurd hc hh,
        fun _ k => ?_⟩
      · funext n
        simp [Vpow, (S.curve c).2.1]
      · intro i n hn
        simp only [Pi.sub_apply, S.pure c i n hn, Vpow]
        split_ifs with hi
        · simp
        · rw [hzp (i - 1) n, sub_zero]
          rw [Nat.cast_sub (by omega)]
          intro hh; apply hn; rw [hh]; push_cast; ring
      · simp [Vpow, hz0]
    · exact ⟨S.cur c, S.curve c, fun _ => rfl, fun hh => absurd hh hc⟩
  choose y h1 h2 h3 using this
  exact ⟨⟨S.tan, y, h1, S.unimod⟩, h2, rfl, h3⟩

theorem stepA [IsAlgClosed C] (S : Sys X) (b : ZMod d) (Q : Finset I) (hQ : ∀ c ∈ Q, X.ty (Sum.inl c) = b)
    (L : AddSubgroup (I → C)) (hL : Stable V L) (hQL : ∀ c ∈ Q, S.tan c ∈ L) :
    ∃ (S' : Sys X) (Q' : Finset I), Q' ⊆ Q ∧
      Q.card ≤ Q'.card + (Finset.univ.filter fun k => X.ty (Sum.inl k) = b + 1).card ∧
      (∀ c, c ∉ Q → S'.cur c = S.cur c) ∧ (∀ c ∈ Q, S'.tan c ∈ L) ∧
      ∀ c ∈ Q', ∀ k, S'.cur c 1 (Sum.inl k) = 0 := by
  obtain ⟨P, Q', hP, h1, h2, h3⟩ := elim_frob (V := V) Q (fun x k => (V.l : C) * S.cur x 1 (Sum.inl k))
    (fun x k => by simpa using (X.bound0 1 _ (S.mem x) (Sum.inl k)).l_mul)
    (Finset.univ.filter fun k => X.ty (Sum.inl k) = b + 1) 1
  obtain ⟨S1, a1, a2, a3⟩ := change S b Q hQ L hL hQL P hP
  obtain ⟨S2, b1, b2, b3⟩ := modify S1 Q' (by
    intro c hc k
    by_cases hk : X.ty (Sum.inl k) = b + 1
    · have := h3 c hc k (by simpa using hk)
      have e : ∑ x, P c x ^ V.l ^ 1 * ((V.l : C) * S.cur x 1 (Sum.inl k)) =
          (V.l : C) * S1.cur c 1 (Sum.inl k) := by
        rw [a3, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      rw [e] at this
      simpa using this.of_l_mul
    · rw [S1.pure c 1 _ (by rw [hQ c (h1 hc)]; simpa using hk)]
      exact VF.Ge.zero 0)
  refine ⟨S2, Q', h1, h2, fun c hc => ?_, fun c hc => ?_, b3⟩
  · rw [b1 c (fun hh => hc (h1 hh)), a1 c hc]
  · rw [b2]; exact a2 c hc

theorem stepB [IsAlgClosed C] (S : Sys X) (b : ZMod d) (Q : Finset I) (hQ : ∀ c ∈ Q, X.ty (Sum.inl c) = b)
    (L : AddSubgroup (I → C)) (hL : Stable V L) (hQL : ∀ c ∈ Q, S.tan c ∈ L)
    (hG : ∀ c ∈ Q, ∀ k, S.cur c 1 (Sum.inl k) = 0) (E : Finset I) :
    ∃ (S' : Sys X) (Q' : Finset I), Q' ⊆ Q ∧ Q.card ≤ Q'.card + E.card ∧
      (∀ c, c ∉ Q → S'.cur c = S.cur c) ∧ (∀ c ∈ Q, S'.tan c ∈ L) ∧
      (∀ c ∈ Q, ∀ k, S'.cur c 1 (Sum.inl k) = 0) ∧
      ∀ c ∈ Q', ∃ g lam : I → C, (∀ e, V.Ge 0 (g e)) ∧ (∀ e, V.Ge 0 (lam e)) ∧
        (∀ e, g e ≠ 0 → X.ty (Sum.inl e) = b + 2 ∧ e ∉ E) ∧
        ∀ k, (V.l : C) * S'.cur c 2 (Sum.inl k) = ∑ e, g e * S.tan e k + (V.l : C) * lam k := by
  have lpos : ∀ k : ℕ, V.l ^ k ≠ 0 := fun k => (pow_pos V.l_prime.pos k).ne'
  set w : I → I → C := fun x e => if x ∈ Q then S.co (fun n => (V.l : C) * S.cur x 2 n) e else 0 with hw
  have hwi : ∀ x e, V.Ge 0 (w x e) := by
    intro x e
    simp only [hw]
    split_ifs with hx
    · refine S.co_int (fun n => ?_) e
      have hg : X.Good _ _ (S.cur x) := ⟨S.curve x, hG x hx⟩
      simpa using (hg.bound 0 n).l_mul
    · exact VF.Ge.zero 0
  obtain ⟨P, Q', hP, h1, h2, h3⟩ := elim_frob (V := V) Q w hwi E 2
  obtain ⟨S1, a1, a2, a3⟩ := change S b Q hQ L hL hQL P hP
  refine ⟨S1, Q', h1, h2, a1, a2, fun c hc k => ?_, fun c hc => ?_⟩
  · rw [a3]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x ∈ Q
    · rw [hG x hx, mul_zero]
    · rw [hP.2.2.2 c hc x hx, zero_pow (lpos 1), zero_mul]
  set W : I → C := fun e => ∑ x, P c x ^ V.l ^ 2 * w x e with hW
  have hWi : ∀ e, V.Ge 0 (W e) := fun e => VF.Ge.sum fun x _ => ((hP.1 _ _).pow _).mul_int (hwi _ _)
  have hmain : ∀ k, (V.l : C) * S1.cur c 2 (Sum.inl k) = ∑ e, W e * S.tan e k := by
    intro k
    rw [a3, Finset.mul_sum]
    simp only [hW, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ Q
    · have := S.co_spec (fun n => (V.l : C) * S.cur x 2 n) k
      simp only [mul_assoc, ← Finset.mul_sum, hw, if_pos hx]
      rw [show ∑ e, S.co (fun n => (V.l : C) * S.cur x 2 n) e * S.tan e k =
        (V.l : C) * S.cur x 2 (Sum.inl k) from this]
      ring
    · simp [hP.2.2.2 c (h1 hc) x hx, zero_pow (lpos 2)]
  refine ⟨fun e => if X.ty (Sum.inl e) = b + 2 ∧ e ∉ E then W e else 0,
    fun k => if X.ty (Sum.inl k) = b + 2 then (V.l : C)⁻¹ * ∑ e ∈ E, W e * S.tan e k else 0,
    fun e => ?_, fun k => ?_, fun e he => ?_, fun k => ?_⟩
  · dsimp only; split_ifs
    · exact hWi e
    · exact VF.Ge.zero 0
  · dsimp only; split_ifs
    · have : V.Ge 1 (∑ e ∈ E, W e * S.tan e k) := VF.Ge.sum fun e he => by
        rw [mul_comm]; exact (S.U_int e k).mul_int (h3 c hc e he)
      simpa using this.l_inv_mul
    · exact VF.Ge.zero 0
  · by_contra hh; exact he (if_neg hh)
  · dsimp only
    by_cases hk : X.ty (Sum.inl k) = b + 2
    · rw [if_pos hk, mul_inv_cancel_left₀ VF.l_ne_zero, hmain, ← Finset.sum_ite_mem_eq E,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : e ∈ E
      · simp [he]
      · by_cases he' : X.ty (Sum.inl e) = b + 2
        · simp [he, he']
        · simp [he, he', tan_pure S (c := e) (k := k) (by rw [hk]; exact Ne.symm he')]
    · rw [if_neg hk, S1.pure c 2 _ (by rw [hQ c (h1 hc)]; simpa using hk), mul_zero, add_zero]
      symm
      refine Finset.sum_eq_zero fun e _ => ?_
      split_ifs with he
      · rw [tan_pure S (by rw [he.1]; exact hk), mul_zero]
      · rw [zero_mul]

theorem chain [IsAlgClosed C] (j' : ℕ) (K : ℕ) : (∀ s, 0 < s → s < K → ((2 * s : ℕ) : ZMod d) ≠ 0) →
    ∀ (a : ZMod d), (∀ s < K, (Finset.univ.filter fun k =>
      X.ty (Sum.inl k) = a + ((2 * s : ℕ) : ZMod d) + 1).card ≤ j') →
    ∀ (S : Sys X) (Q : Finset I), (∀ c ∈ Q, X.ty (Sum.inl c) = a) →
    ∀ (L : AddSubgroup (I → C)), Stable V L → (∀ c ∈ Q, S.tan c ∈ L) →
    ∃ (S' : Sys X) (lev : I → ℕ),
      (∀ c, (∀ s < K, X.ty (Sum.inl c) ≠ a + ((2 * s : ℕ) : ZMod d)) → S'.cur c = S.cur c) ∧
      (∀ c, lev c < K → X.ty (Sum.inl c) = a + ((2 * lev c : ℕ) : ZMod d) ∧
        ∀ k, S'.cur c 1 (Sum.inl k) = 0) ∧
      (∀ c ∈ Q, lev c = 0 → S'.tan c ∈ L) ∧
      Q.card ≤ (Q.filter fun c => lev c = 0).card + K * j' ∧
      ∀ c, lev c + 1 < K → ∃ g lam : I → C, (∀ e, V.Ge 0 (g e)) ∧ (∀ e, V.Ge 0 (lam e)) ∧
        (∀ e, lev e ≠ lev c + 1 → g e = 0) ∧
        ∀ k, (V.l : C) * S'.cur c 2 (Sum.inl k) = ∑ e, g e * S'.tan e k + (V.l : C) * lam k := by
  induction K with
  | zero =>
    intro _ a _ S Q _ L _ hQL
    exact ⟨S, fun _ => 0, fun _ _ => rfl, by simp, fun c hc _ => hQL c hc, by simp, by simp⟩
  | succ K ih =>
    intro hd a hsm S Q hQ L hL hQL
    have hsh : ∀ s : ℕ, a + 2 + ((2 * s : ℕ) : ZMod d) = a + ((2 * (s + 1) : ℕ) : ZMod d) := by
      intro s; push_cast; ring
    have hne : ∀ s < K, a + 2 + ((2 * s : ℕ) : ZMod d) ≠ a := by
      intro s hs h
      rw [hsh] at h
      exact hd (s + 1) (by omega) (by omega) (by simpa using h)
    set T := Finset.univ.filter fun k => X.ty (Sum.inl k) = a + 2 with hT
    obtain ⟨S1, lev, p1, p2, -, p4, p5⟩ := ih (fun s h1 h2 => hd s h1 (by omega)) (a + 2)
      (fun s hs => by rw [hsh]; exact hsm (s + 1) (by omega)) S T (fun c hc => by simpa [hT] using hc)
      ⊤ (fun _ _ _ _ => trivial) (fun _ _ => trivial)
    have hS1 : ∀ c ∈ Q, S1.cur c = S.cur c := fun c hc =>
      p1 c fun s hs => by rw [hQ c hc]; exact (hne s hs).symm
    have hnQ : ∀ c, lev c < K → c ∉ Q := fun c hc hh => hne _ hc (by rw [← (p2 c hc).1, hQ c hh])
    obtain ⟨S2, Q2, q1, q2, q3, q4, q5⟩ := stepA S1 a Q hQ L hL
      (fun c hc => by rw [tan_eq (hS1 c hc)]; exact hQL c hc)
    obtain ⟨S3, Q3, r1, r2, r3, r4, r5, r6⟩ := stepB S2 a Q2 (fun c hc => hQ c (q1 hc)) L hL
      (fun c hc => q4 c (q1 hc)) q5 (T.filter fun c => ¬ lev c = 0)
    have h31 : ∀ c, c ∉ Q → S3.cur c = S1.cur c := fun c hc => by
      rw [r3 c (fun hh => hc (q1 hh)), q3 c hc]
    have hQ3 : ∀ c ∈ Q3, c ∈ Q := fun c hc => q1 (r1 hc)
    refine ⟨S3, fun c => if c ∈ Q3 then 0 else lev c + 1, fun c hc => ?_, fun c hc => ?_,
      fun c hc h0 => ?_, ?_, fun c hc => ?_⟩
    · rw [h31 c (fun hh => hc 0 (by omega) (by simpa using hQ c hh))]
      exact p1 c fun s hs => by rw [hsh]; exact hc (s + 1) (by omega)
    · by_cases h : c ∈ Q3
      · simp only [if_pos h]
        exact ⟨by simpa using hQ c (hQ3 c h), r5 c (r1 h)⟩
      · simp only [if_neg h] at hc ⊢
        have hc' : lev c < K := by omega
        rw [h31 c (hnQ c hc'), ← hsh]
        exact p2 c hc'
    · by_cases h : c ∈ Q3
      · exact r4 c (r1 h)
      · simp [h] at h0
    · have e1 : Q3.card ≤ (Q.filter fun c => (if c ∈ Q3 then 0 else lev c + 1) = 0).card :=
        Finset.card_le_card fun c hc => by simp [hc, hQ3 c hc]
      have e2 := Finset.card_filter_add_card_filter_not (s := T) (fun c => lev c = 0)
      have e3 := hsm 0 (by omega)
      simp only [mul_zero, Nat.cast_zero, add_zero] at e3
      rw [Nat.succ_mul]
      beta_reduce
      omega
    · by_cases h : c ∈ Q3
      · simp only [if_pos h] at hc ⊢
        obtain ⟨g, lam, g1, g2, g3, g4⟩ := r6 c h
        have hg : ∀ e, g e ≠ 0 → e ∉ Q ∧ lev e = 0 := by
          intro e he
          obtain ⟨t1, t2⟩ := g3 e he
          have t3 : lev e = 0 := by
            by_contra hh; exact t2 (by simp [hT, t1, hh])
          exact ⟨hnQ e (by omega), t3⟩
        refine ⟨g, lam, g1, g2, fun e he => ?_, fun k => ?_⟩
        · by_contra hh
          obtain ⟨t1, t2⟩ := hg e hh
          apply he
          rw [if_neg (fun h3 => t1 (hQ3 e h3)), t2]
        · rw [g4]
          congr 1
          refine Finset.sum_congr rfl fun e _ => ?_
          by_cases hh : g e = 0
          · simp [hh]
          · rw [tan_eq (r3 e fun h2 => (hg e hh).1 (q1 h2))]
      · simp only [if_neg h] at hc ⊢
        obtain ⟨g, lam, g1, g2, g3, g4⟩ := p5 c (by omega)
        have hg : ∀ e, g e ≠ 0 → e ∉ Q ∧ lev e = lev c + 1 := by
          intro e he
          have t3 : lev e = lev c + 1 := by
            by_contra hh; exact he (g3 e hh)
          exact ⟨hnQ e (by omega), t3⟩
        refine ⟨g, lam, g1, g2, fun e he => ?_, fun k => ?_⟩
        · by_contra hh
          obtain ⟨t1, t2⟩ := hg e hh
          apply he
          rw [if_neg (fun h3 => t1 (hQ3 e h3)), t2]
        · rw [h31 c (hnQ c (by omega)), g4]
          congr 1
          refine Finset.sum_congr rfl fun e _ => ?_
          by_cases hh : g e = 0
          · simp [hh]
          · rw [tan_eq (h31 e (hg e hh).1)]

def intSpan (V : VF C) {ι : Type} [Fintype ι] (U : ι → I → C) : AddSubgroup (I → C) where
  carrier := {u | ∃ A : ι → C, (∀ b, V.Ge 0 (A b)) ∧ ∀ x, u x = ∑ b, A b * U b x}
  zero_mem' := ⟨0, fun _ => VF.Ge.zero 0, by simp⟩
  add_mem' := by
    rintro u u' ⟨A, h1, h2⟩ ⟨A', h1', h2'⟩
    exact ⟨A + A', fun b => (h1 b).add (h1' b), fun x => by
      simp [h2, h2', add_mul, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro u ⟨A, h1, h2⟩
    exact ⟨-A, fun b => (h1 b).neg, fun x => by simp [h2]⟩

theorem stable_intSpan {ι : Type} [Fintype ι] (U : ι → I → C) : Stable V (intSpan V U) := by
  rintro r hr u ⟨A, h1, h2⟩
  exact ⟨fun b => r * A b, fun b => hr.mul_int (h1 b), fun x => by
    simp [h2, Finset.mul_sum, mul_assoc]⟩

theorem adapted (X : Cart V d I J) {ι : Type} [Fintype ι] (U : ι → I → C) (w : I → ι → C)
    (hU : ∀ c x, V.Ge 0 (U c x)) (hw : ∀ x c, V.Ge 0 (w x c))
    (h : ∀ c c', ∑ x, U c x * w x c' = if c = c' then 1 else 0) (a : ZMod d)
    (ha : ∀ c x, X.ty (Sum.inl x) ≠ a → U c x = 0) :
    ∃ (S : Sys X) (Q : Finset I), (∀ c ∈ Q, X.ty (Sum.inl c) = a) ∧ Q.card = Fintype.card ι ∧
      ∀ c ∈ Q, S.tan c ∈ intSpan V U := by
  obtain ⟨f, hf⟩ := exists_unit_minor U w hU hw h
  have hne : (Matrix.of fun c' c => U c (f c')).det ≠ 0 := by
    intro h0
    rw [h0, V.v.map_zero] at hf
    exact WithTop.top_ne_zero hf
  have hinj : Function.Injective f := by
    intro c c' hcc
    by_contra hh
    exact hne (Matrix.det_zero_of_row_eq hh (by funext b; simp [hcc]))
  have hty : ∀ c, X.ty (Sum.inl (f c)) = a := by
    intro c
    by_contra hh
    exact hne (Matrix.det_eq_zero_of_row_eq_zero c (fun b => ha b _ hh))
  set F : Matrix I ι C := Matrix.of fun x c => if x = f c then 1 else 0 with hF
  set D : Matrix ι I C := Matrix.of fun c y => U c y - if y = f c then 1 else 0 with hD
  have hrow : ∀ c y, (1 + F * D : Matrix I I C) (f c) y = U c y := by
    intro c y
    simp [hF, hD, Matrix.mul_apply, hinj.eq_iff, Matrix.one_apply, eq_comm]
  have hrow' : ∀ x, (∀ c, x ≠ f c) → ∀ y, (1 + F * D : Matrix I I C) x y = if x = y then 1 else 0 := by
    intro x hx y
    simp [hF, Matrix.mul_apply, hx, Matrix.one_apply]
  have hdet : (1 + F * D).det = (Matrix.of fun c' c => U c (f c')).det := by
    rw [Matrix.det_one_add_mul_comm, ← Matrix.det_transpose]
    congr 1
    ext c' c
    simp [hF, hD, Matrix.mul_apply, hinj.eq_iff, Matrix.one_apply, eq_comm]
  obtain ⟨S, hS⟩ := sysExists X (fun x y => (1 + F * D : Matrix I I C) x y)
    (fun x y => by
      by_cases hx : ∃ c, x = f c
      · obtain ⟨c, rfl⟩ := hx
        rw [hrow]; exact hU _ _
      · push_neg at hx
        rw [hrow' x hx]
        split_ifs
        · exact VF.Ge.one
        · exact VF.Ge.zero 0)
    (fun x y hxy => by
      by_cases hx : ∃ c, x = f c
      · obtain ⟨c, rfl⟩ := hx
        rw [hrow]; exact ha _ _ (by rwa [hty] at hxy)
      · push_neg at hx
        rw [hrow' x hx, if_neg (fun hh : x = y => hxy (by rw [hh]))])
    (by rw [← hf, ← hdet]; rfl)
  refine ⟨S, Finset.univ.image f, fun c hc => ?_, ?_, fun c hc => ?_⟩
  · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hc; exact hty b
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨fun b' => if b' = b then 1 else 0, fun b' => ?_, fun x => ?_⟩
    · dsimp only; split_ifs
      · exact VF.Ge.one
      · exact VF.Ge.zero 0
    · rw [hS]; simp only [hrow]; simp

theorem even_val_iff {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) (s : ℕ) :
    Even (a + ((2 * s : ℕ) : ZMod d) + 1).val ↔ ¬ Even a.val := by
  have h2 : 2 ∣ d := hd.two_dvd
  have e : a + ((2 * s : ℕ) : ZMod d) + 1 = ((a.val + 2 * s + 1 : ℕ) : ZMod d) := by
    push_cast; simp
  rw [e, ZMod.val_natCast, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2]
  omega

theorem co_ge (S : Sys X) {r : ℝ} {h : I ⊕ J → C} (hh : ∀ k, V.Ge r (h (Sum.inl k))) (b : I) :
    V.Ge r (S.co h b) :=
  VF.Ge.sum fun k _ => by rw [mul_comm]; exact (inv_int S.U S.U_int S.unimod k b).mul_int (hh k)

theorem co_two (S : Sys X) (h : I ⊕ J → C) (g lam : I → C)
    (e : ∀ k, (V.l : C) * h (Sum.inl k) = ∑ e, g e * S.tan e k + (V.l : C) * lam k) (b : I) :
    S.co h b = (V.l : C)⁻¹ * (g b + (V.l : C) * S.co (Sum.elim lam 0) b) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have h2 : ∑ k, (∑ e, g e * S.tan e k) * S.U⁻¹ k b = g b := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ e, ∑ k, g e * S.tan e k * S.U⁻¹ k b = g e * (S.U * S.U⁻¹) e b := by
      intro e
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp [Sys.U, mul_assoc]
    simp [this, h1, Matrix.one_apply]
  rw [eq_inv_mul_iff_mul_eq₀ VF.l_ne_zero, ← h2]
  simp only [Sys.co, Finset.mul_sum, ← mul_assoc, e, add_mul, Finset.sum_add_distrib, Sum.elim_inl]

theorem adaptedChainData : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type)
    [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.AdaptedChainData := by
  intro C _ V d _ I J _ _ X hAlt g a hbig i hi hid U hU
  haveI := X.algClosed
  obtain ⟨⟨hUi, w, hw, hUw⟩, hUa⟩ := hU
  obtain ⟨S0, Q, hQ, hcard, hQL⟩ := adapted (X.G g) U w hUi hw (fun c c' => by
    rw [hUw]; congr) a hUa
  have hK : 0 < Formalism.BaseCaseIdentities.Kn i ∧ 2 * Formalism.BaseCaseIdentities.Kn i = i + 1 := by
    obtain ⟨m, rfl⟩ := hi; unfold Formalism.BaseCaseIdentities.Kn; omega
  have hsmall : ∀ s : ℕ, ¬ X.big g (a + ((2 * s : ℕ) : ZMod d) + 1) := by
    intro s
    have e := even_val_iff hAlt.1 a s
    have hg : g = 0 ∨ g = 1 - 0 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · rw [hAlt.2] at hbig ⊢; tauto
    · rw [X.big_compl, hAlt.2] at hbig ⊢; tauto
  obtain ⟨S, lev, -, p2, p3, p4, p5⟩ := chain (X := X.G g) X.j' (Formalism.BaseCaseIdentities.Kn i)
    (fun s h0 h1 h => by
      rw [ZMod.natCast_eq_zero_iff] at h
      have := Nat.le_of_dvd (by omega) h
      omega) a
    (fun s _ => by
      refine le_of_eq ?_
      rw [← X.rk_small g _ (hsmall s)]) S0 Q hQ _ (stable_intSpan U) hQL
  have hgood : ∀ c, lev c < Formalism.BaseCaseIdentities.Kn i → (X.G g).Good _ _ (S.cur c) :=
    fun c hc => ⟨S.curve c, (p2 c hc).2⟩
  have hex : ∀ c, ∃ gg lam : I g → C, (∀ e, V.Ge 0 (gg e)) ∧ (∀ e, V.Ge 0 (lam e)) ∧
      (lev c + 1 < Formalism.BaseCaseIdentities.Kn i → ∀ e, lev e ≠ lev c + 1 → gg e = 0) ∧
      (lev c < Formalism.BaseCaseIdentities.Kn i → ∀ b, S.co (S.cur c 2) b = (V.l : C)⁻¹ * (gg b + (V.l : C) * lam b)) := by
    intro c
    by_cases h1 : lev c + 1 < Formalism.BaseCaseIdentities.Kn i
    · obtain ⟨gg, lam, g1, g2, g3, g4⟩ := p5 c h1
      exact ⟨gg, S.co (Sum.elim lam 0), g1, co_ge S g2, fun _ => g3, fun _ => co_two S _ gg lam g4⟩
    · by_cases h2 : lev c < Formalism.BaseCaseIdentities.Kn i
      · refine ⟨fun b => (V.l : C) * S.co (S.cur c 2) b, 0, fun b => ?_, fun _ => VF.Ge.zero 0,
          fun h => absurd h h1, fun _ b => by simp [VF.l_ne_zero]⟩
        simpa using (co_ge S (fun k => (hgood c h2).bound 0 (Sum.inl k)) b).l_mul
      · exact ⟨0, 0, fun _ => VF.Ge.zero 0, fun _ => VF.Ge.zero 0, fun h => absurd h h1,
          fun h => absurd h h2⟩
  choose gg lam g1 g2 g3 g4 using hex
  set Q0 := Q.filter fun c => lev c = 0 with hQ0
  have hmem : ∀ δ, (Q0.equivFin.symm δ).1 ∈ Q ∧ lev (Q0.equivFin.symm δ).1 = 0 :=
    fun δ => Finset.mem_filter.mp (Q0.equivFin.symm δ).2
  have hl3 : 3 ≤ V.l := by
    have := V.l_prime.two_le
    have := X.l_odd
    omega
  choose A hA1 hA2 using fun δ => p3 _ (hmem δ).1 (hmem δ).2
  refine ⟨S, Q0.card,
    { v := V.v, l := V.l, l_prime := V.l_prime, l_ge := hl3, v_l := V.v_l, i := i, i_odd := hi,
      good := fun c => lev c < Formalism.BaseCaseIdentities.Kn i, lev := lev, pure_good := fun _ h => h,
      ι := fun δ => (Q0.equivFin.symm δ).1,
      ι_inj := Subtype.val_injective.comp Q0.equivFin.symm.injective,
      ι_lev := fun δ => (hmem δ).2,
      al := fun c k b => S.co (S.cur c k) b, g := gg, lam := lam,
      al_all := fun c j b => co_ge S (fun k => lattice_inclusion_forms_injective _ S c j _) b,
      al_good := fun c hc j b hj => co_ge S (eq16 _ _ _ _ (hgood c hc) j hj).1 b,
      al_one := fun c hc b => by simp [Sys.co, (p2 c hc).2],
      al_two := g4, g_int := g1, lam_int := g2, g_supp := g3 },
    rfl, rfl, rfl, fun c k x _ => ?_, fun c hc => (p2 c hc).1, ?_, A, hA1, fun δ x => ?_⟩
  · simp only [Sys.al, S.cur_zero_inl]
    exact (S.co_spec (S.cur c k) x).symm
  · rw [hcard, Fintype.card_fin] at p4
    rw [Nat.succ_mul]
    omega
  · simp only [Sys.al, S.cur_zero_inl]
    exact hA2 δ x

end GlobalTheory.AdaptedChain
