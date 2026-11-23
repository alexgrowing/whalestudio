import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Interface

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.TeichPair

theorem iter_frob {k O : Type} [CommRing k] [CommRing O] {d : ℕ} {l : ℕ} (f : ZMod d → O →+* k)
    (hf : ∀ a x, f (a + 1) x = f a x ^ l) (a : ZMod d) (x : O) (n : ℕ) : f (a + n) x = f a x ^ l ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, ← add_assoc, hf, ih, ← pow_mul, pow_succ]

theorem exists_sep {k O : Type} [CommRing k] [IsDomain k] [CommRing O] {d : ℕ} [NeZero d] {l : ℕ} (hl : 2 ≤ l)
    (f : ZMod d → O →+* k) (hf : ∀ a x, f (a + 1) x = f a x ^ l)
    (hsep : ∀ a a', a ≠ a' → ∃ x, f a x ≠ f a' x) :
    ∃ x, (∀ a, f a x ≠ 0) ∧ Function.Injective fun a => f a x := by
  have hq : 2 ≤ l ^ d := le_trans hl (Nat.le_self_pow (NeZero.ne d) l)
  have hv : ∀ a x, f a x = f 0 x ^ l ^ a.val := fun a x => by
    rw [← iter_frob f hf]; simp
  have hd : ∀ x, f 0 x ^ l ^ d = f 0 x := fun x => by
    rw [← iter_frob f hf]; simp
  obtain ⟨N, hN⟩ : ∃ N, l ^ d = N + 2 := ⟨l ^ d - 2, by omega⟩
  have hu : ∀ x, f 0 x ≠ 0 → f 0 x ^ (N + 1) = 1 := fun x hx => by
    apply mul_right_cancel₀ hx
    rw [← pow_succ, one_mul, show N + 1 + 1 = l ^ d by omega, hd]
  let H : Subgroup kˣ :=
    { carrier := {u | ∃ x, f 0 x = u}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro a b ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x * y, by simp [hx, hy]⟩
      inv_mem' := by
        rintro a ⟨x, hx⟩
        refine ⟨x ^ N, ?_⟩
        have h1 := hu x (by rw [hx]; exact a.ne_zero)
        rw [map_pow, hx]
        rw [hx, pow_succ] at h1
        exact (Units.inv_eq_of_mul_eq_one_left h1).symm }
  have hH : H ≤ rootsOfUnity (N + 1) k := by
    rintro a ⟨x, hx⟩
    rw [mem_rootsOfUnity', ← hx]
    exact hu x (by rw [hx]; exact a.ne_zero)
  haveI : IsCyclic H := Subgroup.isCyclic_of_le hH
  obtain ⟨⟨γ, x, hx⟩, hγ⟩ := IsCyclic.exists_zpow_surjective (G := H)
  have hx0 : f 0 x ≠ 0 := by rw [hx]; exact γ.ne_zero
  refine ⟨x, fun a => by rw [hv]; exact pow_ne_zero _ hx0, fun a a' h => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ := hsep a a' hne
  apply hy
  have hl0 : ∀ m : ℕ, l ^ m ≠ 0 := fun m => pow_ne_zero _ (by omega)
  by_cases hy0 : f 0 y = 0
  · rw [hv a, hv a', hy0, zero_pow (hl0 _), zero_pow (hl0 _)]
  · have h1 := hu y hy0
    rw [pow_succ] at h1
    let w : kˣ := Units.mkOfMulEqOne (f 0 y) (f 0 y ^ N) (by rw [mul_comm]; exact h1)
    obtain ⟨m, hm⟩ := hγ ⟨w, y, rfl⟩
    have hm' : γ ^ m = w := congrArg Subtype.val hm
    have h2 : γ ^ l ^ a.val = γ ^ l ^ a'.val := by
      apply Units.ext
      have h' : f a x = f a' x := h
      rw [hv a, hv a', hx] at h'
      simpa using h'
    have h3 : w ^ l ^ a.val = w ^ l ^ a'.val := by
      rw [← hm', ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm m, mul_comm m, zpow_mul, zpow_mul,
        zpow_natCast, zpow_natCast, h2]
    have h4 := congrArg Units.val h3
    rw [hv a, hv a']
    simpa [w] using h4

variable {C : Type} [Field C]

def intRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

def maxId (V : VF C) : Ideal (intRing V) where
  carrier := {x | 0 < V.v (x : C)}
  add_mem' := fun ha hb => V.v.map_lt_add ha hb
  zero_mem' := by
    show 0 < V.v ((0 : intRing V) : C)
    simp
  smul_mem' := fun c x hx => by
    show 0 < V.v ((c : C) * x)
    rw [V.v.map_mul]
    have hc : (0 : WithTop ℝ) ≤ V.v c := c.2
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left hc)

instance maxId_prime (V : VF C) : (maxId V).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]
    show ¬ 0 < V.v ((1 : intRing V) : C)
    simp
  mem_or_mem' := fun {x y} h => by
    by_contra hc
    push Not at hc
    have hx : V.v (x : C) = 0 := le_antisymm (not_lt.1 hc.1) x.2
    have hy : V.v (y : C) = 0 := le_antisymm (not_lt.1 hc.2) y.2
    have h' : 0 < V.v ((x : C) * y) := h
    rw [V.v.map_mul, hx, hy] at h'
    simp at h'

theorem eq_zero_of_ge {V : VF C} {z : C} (h : ∀ N : ℕ, V.Ge N z) : z = 0 := by
  by_contra hz
  have h1 : V.v z ≠ ⊤ := fun h => hz (V.v.top_iff.1 h)
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h1
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have := h N
  unfold VF.Ge at this
  rw [← ht] at this
  exact absurd (WithTop.coe_le_coe.1 this) (not_le.2 hN)

theorem ge_pow_sub {V : VF C} {w : ℝ} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (h : V.Ge w (a - b)) (m : ℕ) :
    V.Ge w (a ^ m - b ^ m) := by
  induction m with
  | zero => simpa using VF.Ge.zero (V := V) w
  | succ m ih =>
    have : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + b ^ m * (a - b) := by ring
    rw [this]
    exact (ha.mul_int ih).add ((hb.pow m).mul_int h)

theorem ge_l_pow (V : VF C) (n : ℕ) : V.Ge n ((V.l : C) ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one (V := V)
  | succ n ih => rw [pow_succ]; push_cast; exact ih.mul VF.ge_l

theorem exists_seq (V : VF C) (cpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    {O : Type} [CommRing O] {d : ℕ} [NeZero d] (e : ZMod d → O →+* C) (hint : ∀ a x, V.Ge 0 (e a x))
    (hfrob : ∀ a x, V.MM (e (a + 1) x - e a x ^ V.l))
    (hsep : ∀ a a', a ≠ a' → ∃ x, V.v (e a x - e a' x) = 0)
    (hunr : ∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (e a ε - 1)) ∧
      ∀ x : O, (∀ a, V.MM (e a x)) → ∃ y, ε * x = (V.l : O) * y) :
    ∃ (s : ℕ → O) (N : ℕ) (ζ : ZMod d → C), (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ V.v (N : C) = 0 ∧
      (∀ a, ζ a ^ N = 1) ∧ Function.Injective ζ ∧ (∀ a, ζ (a + 1) = ζ a ^ V.l) ∧
      ∀ a (n : ℕ), V.Ge n (ζ a - e a (s n)) := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hq : 2 ≤ V.l ^ d := le_trans hl (Nat.le_self_pow (NeZero.ne d) _)
  obtain ⟨N, hN⟩ : ∃ N, V.l ^ d = N + 2 := ⟨V.l ^ d - 2, by omega⟩
  let π := Ideal.Quotient.mk (maxId V)
  have hπ : ∀ a b : intRing V, π a = π b ↔ V.MM ((a : C) - b) := fun a b => Ideal.Quotient.eq
  let e' : ZMod d → O →+* intRing V := fun a => (e a).codRestrict (intRing V) (hint a)
  let f : ZMod d → O →+* (intRing V ⧸ maxId V) := fun a => π.comp (e' a)
  have hf : ∀ a x, f (a + 1) x = f a x ^ V.l := fun a x => by
    show π _ = π _ ^ _
    rw [← map_pow, hπ]
    exact hfrob a x
  have hs : ∀ a a', a ≠ a' → ∃ x, f a x ≠ f a' x := fun a a' h => by
    obtain ⟨x, hx⟩ := hsep a a' h
    refine ⟨x, fun h' => ?_⟩
    have h2 : 0 < V.v (e a x - e a' x) := (hπ _ _).1 h'
    rw [hx] at h2
    exact lt_irrefl _ h2
  obtain ⟨x, hx0, hxi⟩ := exists_sep hl f hf hs
  obtain ⟨ε, ⟨y, hy⟩, hε1, hε⟩ := hunr
  have hd : ∀ a x, f a x ^ V.l ^ d = f a x := fun a x => by
    rw [← iter_frob f hf]; simp
  have hfε : ∀ a, f a ε = 1 := fun a => by
    show π _ = 1
    rw [← map_one π, hπ]
    exact hε1 a
  have hεp : ∀ m : ℕ, (V.l : O) ∣ ε ^ (m + 1) - ε := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      have : ε ^ (m + 1 + 1) - ε = ε * (ε ^ (m + 1) - ε) + (ε * ε - ε) := by ring
      rw [this, hy]
      exact dvd_add (ih.mul_left _) (dvd_mul_right _ _)
  have hb : (V.l : O) ∣ (ε * x) ^ V.l ^ d - ε * x := by
    obtain ⟨z, hz⟩ := hε (x ^ V.l ^ d - x) fun a => by
      have h1 : π (e' a (x ^ V.l ^ d)) = π (e' a x) := by
        show f a _ = f a _
        rw [map_pow, hd]
      rw [map_sub]
      exact (hπ _ _).1 h1
    have : (ε * x) ^ V.l ^ d - ε * x = (ε ^ (N + 1 + 1) - ε) * x ^ V.l ^ d + ε * (x ^ V.l ^ d - x) := by
      rw [mul_pow, show N + 1 + 1 = V.l ^ d by omega]; ring
    rw [this, hz]
    exact dvd_add ((hεp _).mul_right _) (dvd_mul_right _ _)
  let s : ℕ → O := fun n => (ε * x) ^ V.l ^ (d * n)
  have hs1 : ∀ n, s (n + 1) = s n ^ V.l ^ d := fun n => by
    simp only [s]
    rw [← pow_mul, ← pow_add, mul_add, mul_one]
  have hsc : ∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y := fun n => by
    have h1 := dvd_sub_pow_of_dvd_sub hb (d * n)
    have h2 : s (n + 1) = ((ε * x) ^ V.l ^ d) ^ V.l ^ (d * n) := by
      simp only [s]
      rw [← pow_mul, ← pow_add, mul_add, mul_one, add_comm]
    rw [h2]
    refine dvd_trans (pow_dvd_pow _ ?_) h1
    have : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
    nlinarith
  have hlim : ∀ a, ∃ z, ∀ n : ℕ, V.Ge n (z - e a (s n)) := fun a => cpl (fun n => e a (s n)) fun n => by
    obtain ⟨z, hz⟩ := hsc n
    rw [← map_sub, hz, map_mul, map_pow, map_natCast]
    simpa using (ge_l_pow V n).mul (hint a z)
  choose ζ hζ using hlim
  have hζi : ∀ a, V.Ge 0 (ζ a) := fun a => by
    have := (hζ a 0).add (by simpa using hint a (s 0))
    simpa using this
  have hζq : ∀ a, ζ a ^ V.l ^ d = ζ a := fun a => by
    rw [← sub_eq_zero]
    refine eq_zero_of_ge (V := V) fun n => ?_
    have h1 := ge_pow_sub (hζi a) (hint a _) (hζ a n) (V.l ^ d)
    have h2 := (hζ a (n + 1)).mono (w' := n) (by push_cast; linarith)
    rw [hs1, map_pow] at h2
    simpa using h1.sub h2
  let ζ' : ZMod d → intRing V := fun a => ⟨ζ a, hζi a⟩
  have hζπ : ∀ a, π (ζ' a) = f a x := fun a => by
    have h1 : π (ζ' a) = f a (s 1) := by
      refine (hπ _ _).2 (lt_of_lt_of_le ?_ (hζ a 1))
      exact_mod_cast WithTop.coe_lt_coe.2 (zero_lt_one' ℝ)
    rw [h1, hs1, map_pow, hd]
    simp [s, hfε]
  have hζ0 : ∀ a, ζ a ≠ 0 := fun a h => by
    apply hx0 a
    rw [← hζπ, show ζ' a = 0 from Subtype.ext h, map_zero]
  have hζN : ∀ a, ζ a ^ (N + 1) = 1 := fun a => by
    apply mul_right_cancel₀ (hζ0 a)
    rw [← pow_succ, one_mul, show N + 1 + 1 = V.l ^ d by omega, hζq]
  have hlπ : ((V.l : ℕ) : intRing V ⧸ maxId V) = 0 := by
    rw [← map_natCast π, ← map_zero π, hπ]
    show 0 < V.v _
    simp [V.v_l]
  have hNπ : ((N + 1 : ℕ) : intRing V ⧸ maxId V) ≠ 0 := fun h => by
    have h1 : ((N + 1 + 1 : ℕ) : intRing V ⧸ maxId V) = 0 := by
      rw [show N + 1 + 1 = V.l ^ d by omega, Nat.cast_pow, hlπ, zero_pow (NeZero.ne d)]
    rw [Nat.cast_succ, h, zero_add] at h1
    exact one_ne_zero h1
  refine ⟨s, N + 1, ζ, hsc, ?_, hζN, fun a a' h => hxi ?_, fun a => ?_, hζ⟩
  · refine le_antisymm (not_lt.1 fun h => hNπ ?_) (VF.ge_natCast (V := V) _)
    rw [← map_natCast π, ← map_zero π, hπ]
    show 0 < V.v _
    simpa using h
  · show f a x = f a' x
    rw [← hζπ, ← hζπ, show ζ' a = ζ' a' from Subtype.ext h]
  · by_contra hne
    have h1 := geom_sum₂_mul (ζ' (a + 1)) (ζ' a ^ V.l) (N + 1)
    have h2 : ζ' (a + 1) ^ (N + 1) - (ζ' a ^ V.l) ^ (N + 1) = 0 := by
      apply Subtype.ext
      show ζ (a + 1) ^ (N + 1) - (ζ a ^ V.l) ^ (N + 1) = 0
      rw [← pow_mul, mul_comm, pow_mul, hζN, hζN, one_pow, sub_self]
    rw [h2, mul_eq_zero, sub_eq_zero] at h1
    rcases h1 with h1 | h1
    · have h3 := congrArg π h1
      rw [map_sum, map_zero] at h3
      simp only [map_mul, map_pow, hζπ, ← hf] at h3
      rw [geom_sum₂_self] at h3
      exact mul_ne_zero hNπ (pow_ne_zero _ (hx0 _)) h3
    · exact hne (congrArg Subtype.val h1)

end GlobalTheory.TeichPair
