import Formalism.LocalToGlobal.CharacterGerms.GeNatCast

namespace Formalism.L2.FormalSeriesBounds

open Finset

noncomputable section

variable {C : Type*} [Field C] {V : VF C} {d : ℕ} {I J : Type*}

section Ops

variable {N : Type*}

theorem Vpow_zero (x : ℕ → N → C) : Vpow 0 x = x := by
  funext i n
  simp [Vpow]

theorem Vpow_succ (s : ℕ) (x : ℕ → N → C) : Vpow (s + 1) x = Vpow 1 (Vpow s x) := by
  funext i n
  simp only [Vpow]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

end Ops

namespace Cart

variable (X : Cart V d I J)

theorem Vpow_mem (s : ℕ) {x : ℕ → I ⊕ J → C} (hx : x ∈ X.Ty) : Vpow s x ∈ X.Ty := by
  induction s with
  | zero => rw [Vpow_zero]; exact hx
  | succ s ih => rw [Vpow_succ]; exact X.V_mem _ ih

theorem bound0 : ∀ (i : ℕ) (x : ℕ → I ⊕ J → C), x ∈ X.Ty → ∀ n, V.Ge (-(i : ℝ)) (x i n) := by
  intro i
  induction i with
  | zero =>
    intro x hx n
    simpa using X.t2 x hx 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) n
  | succ i ih =>
    intro x hx n
    have := (ih _ (X.F_mem x hx) n).of_l_mul
    exact this.mono (by push_cast; linarith)

def IsCurve (a : ZMod d) (u : I → C) (x : ℕ → I ⊕ J → C) : Prop :=
  x ∈ X.Ty ∧ x 0 = Sum.elim u 0 ∧ ∀ (i : ℕ) n, X.ty n ≠ a + i → x i n = 0

section Std

variable [DecidableEq I]

theorem exists_std (b : I) : ∃ x, X.IsCurve (X.ty (Sum.inl b)) (Pi.single b 1) x := by
  have hu : ∀ c, V.Ge 0 ((Pi.single b (1 : C) : I → C) c) := by
    intro c
    by_cases hc : c = b
    · subst hc
      simpa using (VF.Ge.one (V := V))
    · simpa [Pi.single_apply, hc] using (VF.Ge.zero (V := V) 0)
  have hty : ∀ c, X.ty (Sum.inl c) ≠ X.ty (Sum.inl b) → (Pi.single b (1 : C) : I → C) c = 0 := by
    intro c hc
    have : c ≠ b := fun h => hc (h ▸ rfl)
    simp [Pi.single_apply, this]
  obtain ⟨x, hx, h0, h1⟩ := X.t4 _ _ hu hty
  exact ⟨x, hx, h0, h1⟩

def std (b : I) : ℕ → I ⊕ J → C := Classical.choose (X.exists_std b)

theorem std_spec (b : I) : X.IsCurve (X.ty (Sum.inl b)) (Pi.single b 1) (X.std b) :=
  Classical.choose_spec (X.exists_std b)

variable [Fintype I]

def lift (h : I ⊕ J → C) : ℕ → I ⊕ J → C :=
  (∑ b, teich V.l (h (Sum.inl b)) (X.std b)) + const0 (Sum.elim 0 (fun j => h (Sum.inr j)))

theorem lift_mem {h : I ⊕ J → C} (hh : ∀ n, V.Ge 0 (h n)) : X.lift h ∈ X.Ty := by
  unfold lift
  exact X.Ty.add_mem (X.Ty.sum_mem fun b _ => X.teich_mem _ (hh _) _ (X.std_spec b).1)
    (X.t3 _ fun j => hh _)

theorem lift_apply (h : I ⊕ J → C) (i : ℕ) (n : I ⊕ J) : X.lift h i n =
    (∑ b, h (Sum.inl b) ^ (V.l ^ i) * X.std b i n) +
      const0 (Sum.elim 0 (fun j => h (Sum.inr j))) i n := by
  simp only [lift, Pi.add_apply, Finset.sum_apply, teich]

theorem lift_zero (h : I ⊕ J → C) : X.lift h 0 = h := by
  funext n
  rw [lift_apply]
  simp only [pow_zero, pow_one, (X.std_spec _).2.1, const0, if_pos rfl]
  cases n with
  | inl b' => simp [Pi.single_apply]
  | inr j => simp

theorem boundS : ∀ (i s : ℕ) (x : ℕ → I ⊕ J → C), x ∈ X.Ty → (∀ j < s, x j = 0) →
    ∀ n, V.Ge (-(i : ℝ)) (x (s + i) n) := by
  intro i
  induction i with
  | zero =>
    intro s x hx hz n
    simpa using X.t2 x hx s hz n
  | succ i ih =>
    intro s x hx hz n
    have hint : ∀ m, V.Ge 0 (x s m) := X.t2 x hx s hz
    have hL := X.lift_mem hint
    have hx' : x - Vpow s (X.lift (x s)) ∈ X.Ty := X.Ty.sub_mem hx (X.Vpow_mem s hL)
    have hz' : ∀ j < s + 1, (x - Vpow s (X.lift (x s))) j = 0 := by
      intro j hj
      funext m
      simp only [Pi.sub_apply, Pi.zero_apply, Vpow]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
      · rw [if_pos h, hz j h]
        simp
      · subst h
        rw [if_neg (lt_irrefl _), Nat.sub_self, X.lift_zero, sub_self]
    have h1 := ih (s + 1) _ hx' hz' n
    have h2 := X.bound0 (i + 1) _ hL n
    have hsplit : x (s + (i + 1)) n =
        (x - Vpow s (X.lift (x s))) (s + 1 + i) n + X.lift (x s) (i + 1) n := by
      simp only [Pi.sub_apply, Vpow]
      rw [if_neg (by omega), show s + 1 + i - s = i + 1 by omega, show s + 1 + i = s + (i + 1) by omega]
      ring
    rw [hsplit]
    exact (h1.mono (by push_cast; linarith)).add h2

def rem (x : ℕ → I ⊕ J → C) : ℕ → (ℕ → I ⊕ J → C)
  | 0 => x
  | s + 1 => rem x s - Vpow s (X.lift (rem x s s))

theorem rem_eq (x : ℕ → I ⊕ J → C) (s : ℕ) :
    X.rem x s = x - ∑ s' ∈ range s, Vpow s' (X.lift (X.rem x s' s')) := by
  induction s with
  | zero => simp [rem]
  | succ s ih =>
    show X.rem x s - Vpow s (X.lift (X.rem x s s)) = _
    rw [Finset.sum_range_succ, sub_add_eq_sub_sub, ← ih]

end Std

def Good (a : ZMod d) (u : I → C) (x : ℕ → I ⊕ J → C) : Prop :=
  X.IsCurve a u x ∧ ∀ c, x 1 (Sum.inl c) = 0

def V2 (_X : Cart V d I J) (x : ℕ → I ⊕ J → C) : I → C := fun b => (V.l : C) * x 2 (Sum.inl b)

def c0' (_X : Cart V d I J) (x : ℕ → I ⊕ J → C) : J → C := fun j => (V.l : C) * x 1 (Sum.inr j)

variable {X}

theorem Good.bound [DecidableEq I] [Fintype I] {a : ZMod d} {u : I → C} {x : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (i : ℕ) (n : I ⊕ J) : V.Ge (-((i : ℝ) + 1)) (x (i + 2) n) := by
  have hx := h.1.1
  have hF := X.F_mem _ hx
  have hζ : ∀ j, V.Ge 0 ((V.l : C) * x 1 (Sum.inr j)) := fun j => by
    have := X.t2 _ hF 0 (fun _ h => absurd h (Nat.not_lt_zero _)) (Sum.inr j)
    exact this
  have hw : Fs V.l x - const0 (Sum.elim 0 (fun j => (V.l : C) * x 1 (Sum.inr j))) ∈ X.Ty :=
    X.Ty.sub_mem hF (X.t3 _ hζ)
  have hw0 : ∀ j < 1, (Fs V.l x - const0 (Sum.elim 0 (fun j => (V.l : C) * x 1 (Sum.inr j))) :
      ℕ → I ⊕ J → C) j = 0 := by
    intro j hj
    obtain rfl : j = 0 := by omega
    funext m
    cases m with
    | inl c => simp [Fs, const0, h.2 c]
    | inr k => simp [Fs, const0]
  have hb := X.boundS i 1 _ hw hw0 n
  have he : (Fs V.l x - const0 (Sum.elim 0 (fun j => (V.l : C) * x 1 (Sum.inr j))) :
      ℕ → I ⊕ J → C) (1 + i) n =
      (V.l : C) * x (i + 2) n := by
    simp only [Pi.sub_apply, Fs, const0]
    rw [if_neg (by omega), sub_zero, show 1 + i + 1 = i + 2 by omega]
  rw [he] at hb
  exact hb.of_l_mul.mono (by linarith)

theorem Good.bound_one {a : ZMod d} {u : I → C} {x : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (n : I ⊕ J) : V.Ge (-1) (x 1 n) := by
  have := X.t2 _ (X.F_mem _ h.1.1) 0 (fun i hi => absurd hi (Nat.not_lt_zero i)) n
  have h2 : V.Ge 0 ((V.l : C) * x 1 n) := this
  exact h2.of_l_mul.mono (by norm_num)

theorem Good.c0'_int {a : ZMod d} {u : I → C} {x : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (j : J) : V.Ge 0 (X.c0' x j) := by
  have := X.t2 _ (X.F_mem _ h.1.1) 0 (fun i hi => absurd hi (Nat.not_lt_zero i)) (Sum.inr j)
  exact this

theorem Good.comb {ι : Type*} (s : Finset ι) {a : ZMod d} {u : ι → I → C}
    {x : ι → ℕ → I ⊕ J → C} {co : ι → C} (hco : ∀ k ∈ s, V.Ge 0 (co k))
    (h : ∀ k ∈ s, X.Good a (u k) (x k)) :
    X.Good a (∑ k ∈ s, co k • u k) (∑ k ∈ s, teich V.l (co k) (x k)) := by
  refine And.intro (And.intro ?_ (And.intro ?_ ?_)) ?_
  · exact X.Ty.sum_mem fun k hk => X.teich_mem _ (hco k hk) _ (h k hk).1.1
  · funext n
    simp only [Finset.sum_apply, teich, pow_zero, pow_one]
    calc ∑ k ∈ s, co k * x k 0 n = ∑ k ∈ s, co k * Sum.elim (u k) 0 n :=
          Finset.sum_congr rfl fun k hk => by rw [(h k hk).1.2.1]
      _ = _ := by cases n <;> simp [Finset.sum_apply]
  · intro i n hn
    simp only [Finset.sum_apply, teich]
    exact Finset.sum_eq_zero fun k hk => by rw [(h k hk).1.2.2 i n hn, mul_zero]
  · intro c
    simp only [Finset.sum_apply, teich]
    exact Finset.sum_eq_zero fun k hk => by rw [(h k hk).2 c, mul_zero]

theorem scaledSecond_sum {ι : Type*} (s : Finset ι) (x : ι → ℕ → I ⊕ J → C) (co : ι → C) (b : I) :
    X.V2 (∑ k ∈ s, teich V.l (co k) (x k)) b = ∑ k ∈ s, co k ^ (V.l ^ 2) * X.V2 (x k) b := by
  simp only [V2, Finset.sum_apply, teich, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem c0'_comb {ι : Type*} (s : Finset ι) (x : ι → ℕ → I ⊕ J → C) (co : ι → C) (j : J) :
    X.c0' (∑ k ∈ s, teich V.l (co k) (x k)) j = ∑ k ∈ s, co k ^ V.l * X.c0' (x k) j := by
  simp only [c0', Finset.sum_apply, teich, pow_one, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem Good.wd {a : ZMod d} {u : I → C} {x x' : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (h' : X.Good a u x') (n : I ⊕ J) : V.Ge 0 (x 2 n - x' 2 n) := by
  have hz : x - x' ∈ X.Ty := X.Ty.sub_mem h.1.1 h'.1.1
  have hz0 : (x - x') 0 = 0 := by rw [Pi.sub_apply, h.1.2.1, h'.1.2.1, sub_self]
  have hγ : ∀ j, V.Ge 0 (x 1 (Sum.inr j) - x' 1 (Sum.inr j)) := fun j => by
    have := X.t2 _ hz 1 (fun i hi => by rw [show i = 0 by omega]; exact hz0) (Sum.inr j)
    simpa using this
  have hw : (x - x') - Vpow 1 (const0 (Sum.elim 0 (fun j => x 1 (Sum.inr j) - x' 1 (Sum.inr j)))) ∈ X.Ty :=
    X.Ty.sub_mem hz (X.V_mem _ (X.t3 _ hγ))
  have hw0 : ∀ i < 2, ((x - x') - Vpow 1 (const0 (Sum.elim 0
      (fun j => x 1 (Sum.inr j) - x' 1 (Sum.inr j)))) : ℕ → I ⊕ J → C) i = 0 := by
    intro i hi
    funext m
    interval_cases i
    · simp [Vpow, h.1.2.1, h'.1.2.1]
    · cases m with
      | inl c => simp [Vpow, const0, h.2 c, h'.2 c]
      | inr j => simp [Vpow, const0]
  have hw2 := X.t2 _ hw 2 hw0 n
  simpa [Vpow, const0] using hw2

end Cart

end

end Formalism.L2.FormalSeriesBounds
