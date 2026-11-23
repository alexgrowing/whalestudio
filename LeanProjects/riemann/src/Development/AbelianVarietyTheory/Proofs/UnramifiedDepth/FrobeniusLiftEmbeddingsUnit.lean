import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqOfMapEqOfPowEqOne
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.TeichSeq

theorem frob_iter {O k : Type} [CommRing O] [CommRing k] {d : ℕ} (l : ℕ)
    (φ : ZMod d → (O →+* k)) (h : ∀ a x, φ (a + 1) x = φ a x ^ l) (a : ZMod d) (x : O) (n : ℕ) :
    φ (a + n) x = φ a x ^ l ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, ← add_assoc, h, ih, ← pow_mul, pow_succ]

theorem exists_separating {O k : Type} [CommRing O] [CommRing k] [IsDomain k] {d : ℕ} [NeZero d]
    (l : ℕ) (hl : 1 < l) (φ : ZMod d → (O →+* k)) (h : ∀ a x, φ (a + 1) x = φ a x ^ l)
    (hs : ∀ a a', a ≠ a' → ∃ x, φ a x ≠ φ a' x) :
    ∃ x, (∀ a, φ a x ≠ 0) ∧ Function.Injective (fun a => φ a x) := by
  classical
  have hq : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) hl
  have hper : ∀ x, φ 0 x ^ l ^ d = φ 0 x := fun x => by
    rw [← frob_iter l φ h]; simp
  have hval : ∀ a x, φ a x = φ 0 x ^ l ^ a.val := fun a x => by
    rw [← frob_iter l φ h]; simp
  have hfin : ((φ 0).range : Set k).Finite := by
    have hne : (Polynomial.X ^ l ^ d - Polynomial.X : Polynomial k) ≠ 0 :=
      (Polynomial.monic_X_pow_sub (by
        rw [Polynomial.degree_X]; exact_mod_cast hq)).ne_zero
    refine (Polynomial.finite_setOf_isRoot hne).subset ?_
    rintro _ ⟨x, rfl⟩
    simp [hper]
  haveI : Finite (φ 0).range := hfin
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := ((φ 0).range)ˣ)
  obtain ⟨x, hx⟩ := (g : (φ 0).range).2
  have hx0 : φ 0 x ≠ 0 := by
    rw [hx]; intro h0
    exact g.ne_zero (Subtype.ext h0)
  refine ⟨x, fun a => by rw [hval]; exact pow_ne_zero _ hx0, fun a a' haa => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ := hs a a' hne
  apply hy
  simp only at haa
  rw [hval a, hval a'] at haa ⊢
  by_cases hy0 : φ 0 y = 0
  · rw [hy0, zero_pow (by positivity), zero_pow (by positivity)]
  · have hu : IsUnit (⟨φ 0 y, y, rfl⟩ : (φ 0).range) :=
      ((Finite.isField_of_domain _).mul_inv_cancel
        (fun h0 => hy0 (congrArg Subtype.val h0))).elim fun b hb => IsUnit.of_mul_eq_one b hb
    obtain ⟨u, hu⟩ := hu
    obtain ⟨m, hm⟩ := hg u
    have : φ 0 y = φ 0 x ^ m := by
      rw [hx]
      have := congrArg (fun t : ((φ 0).range)ˣ => ((t : (φ 0).range) : k)) hm
      simp only [hu] at this
      simpa using this.symm
    rw [this, ← pow_mul, ← pow_mul, mul_comm m, mul_comm m, pow_mul, pow_mul, haa]

theorem root_eq {R k : Type} [CommRing R] [IsDomain R] [CommRing k] [IsDomain k] (π : R →+* k)
    {N : ℕ} (hN : (N : k) ≠ 0) {u w : R} (hu : u ^ N = 1) (hw : w ^ N = 1) (h : π u = π w) :
    u = w := by
  first
  | (rename_i h_2 h_3 h_4 h_5; revert R k h_2 h_3 h_4 h_5 π N hN u w hu hw h; exact @_root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one)
  | exact @_root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one
  | exact _root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one
  | (apply _root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootsOfUnityInjective.eq_of_map_eq_of_pow_eq_one ..)

variable {C : Type} [Field C] (V : VF C)

def intRing : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

def maxId : Ideal (intRing V) where
  carrier := {x | V.MM (x : C)}
  add_mem' := fun {a b} ha hb => V.v.map_lt_add ha hb
  zero_mem' := by simp [VF.MM]
  smul_mem' := fun c x hx => by
    have hc : (0 : WithTop ℝ) ≤ V.v c := c.2
    show 0 < V.v ((c : C) * x)
    rw [V.v.map_mul]
    exact lt_of_lt_of_le hx (le_add_of_nonneg_left hc)

instance : (maxId V).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one]
    show ¬ 0 < V.v 1
    simp
  mem_or_mem' := fun {a b} hab => by
    have h : 0 < V.v ((a : C) * b) := hab
    rw [V.v.map_mul] at h
    by_contra hn
    rw [not_or] at hn
    have h1 : V.v a ≤ 0 := not_lt.1 hn.1
    have h2 : V.v b ≤ 0 := not_lt.1 hn.2
    exact absurd h (not_lt.2 (add_nonpos h1 h2))

theorem eq_zero_of_ge {x : C} (h : ∀ n : ℕ, V.Ge n x) : x = 0 := by
  by_contra hx
  have h1 : V.v x ≠ ⊤ := by
    intro ht
    have := V.v.map_mul x x⁻¹
    rw [mul_inv_cancel₀ hx, V.v.map_one, ht, top_add] at this
    exact WithTop.zero_ne_top this
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h1
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have := h n
  unfold VF.Ge at this
  rw [← ht, WithTop.coe_le_coe] at this
  linarith

theorem ge_l_pow (n : ℕ) : V.Ge n ((V.l : C) ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one
  | succ n ih => rw [pow_succ]; push_cast; exact ih.mul VF.ge_l

theorem ge_pow_sub {u w : C} (hu : V.Ge 0 u) (hw : V.Ge 0 w) {t : ℝ} (h : V.Ge t (u - w)) (m : ℕ) :
    V.Ge t (u ^ m - w ^ m) := by
  rw [← (Commute.all u w).geom_sum₂_mul m]
  exact VF.Ge.mul_int (VF.Ge.sum fun i _ => (hu.pow _).mul_int (hw.pow _)) h

theorem mm_of_ge_one {x : C} (h : V.Ge 1 x) : V.MM x :=
  lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)) h

end GlobalTheory.TeichSeq

namespace GlobalTheory

open TeichSeq in

theorem exists_teichmueller_sequence : ∀ (C : Type) [Field C] [CharZero C] (V : VF C), (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → ∀ (O : Type) [CommRing O] (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → (∀ a a' : ZMod d, a ≠ a' → ∃ x, V.v (em a x - em a' x) = 0) → (∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em a ε - 1)) ∧ ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∃ (N : ℕ) (ζ : ZMod d → C) (s : ℕ → O), V.v (N : C) = 0 ∧ (∀ a, ζ a ^ N = 1) ∧ Function.Injective ζ ∧ (∀ a, ζ (a + 1) = ζ a ^ V.l) ∧ (∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y) ∧ ∀ (a : ZMod d) (K : ℕ), ∃ n0, ∀ n ≥ n0, V.Ge K (ζ a - em a (s n)) := by
  intro C _ _ V hcomp O _ d _ em hint hfrob hsep ⟨ε, ⟨y0, hε2⟩, hε1, hεP⟩
  have hl : 1 < V.l := V.l_prime.one_lt
  let π : intRing V →+* intRing V ⧸ maxId V := Ideal.Quotient.mk _
  let e : ZMod d → (O →+* intRing V) := fun a => (em a).codRestrict (intRing V) (hint a)
  let φ : ZMod d → (O →+* intRing V ⧸ maxId V) := fun a => π.comp (e a)
  have hπ : ∀ u w : intRing V, π u = π w ↔ V.MM ((u : C) - w) := fun u w => Ideal.Quotient.eq
  have hφ : ∀ a x, φ (a + 1) x = φ a x ^ V.l := fun a x => by
    show π (e (a + 1) x) = π (e a x) ^ V.l
    rw [← map_pow, hπ]
    exact hfrob a x
  have hs : ∀ a a', a ≠ a' → ∃ x, φ a x ≠ φ a' x := fun a a' haa => by
    obtain ⟨x, hx⟩ := hsep a a' haa
    refine ⟨x, fun h => ?_⟩
    have : 0 < V.v (em a x - em a' x) := (hπ (e a x) (e a' x)).1 h
    rw [hx] at this
    exact lt_irrefl _ this
  obtain ⟨x, hx0, hxinj⟩ := exists_separating V.l hl φ hφ hs
  set q := V.l ^ d with hqdef
  have hq : 1 < q := Nat.one_lt_pow (NeZero.ne d) hl
  have hper : ∀ a y, φ a y ^ q = φ a y := fun a y => by
    rw [← frob_iter V.l φ hφ]; simp
  have hφε : ∀ a, φ a ε = 1 := fun a => (hπ (e a ε) 1).2 (hε1 a)
  have hεpow : ∀ n, (V.l : O) ∣ ε ^ (n + 1) - ε := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have : ε ^ (n + 1 + 1) - ε = (ε ^ (n + 1) - ε) * ε + (ε * ε - ε) := by ring
      rw [this]
      exact dvd_add (ih.mul_right _) ⟨y0, hε2⟩
  have hz : (V.l : O) ∣ (ε * x) ^ q - ε * x := by
    have h1 : (V.l : O) ∣ ε * (x ^ q - x) := by
      refine hεP _ fun a => ?_
      have := (hπ (e a (x ^ q)) (e a x)).1 (by
        show φ a (x ^ q) = φ a x
        rw [map_pow, hper])
      rw [map_sub]
      exact this
    have h2 := hεpow (q - 1)
    rw [Nat.sub_add_cancel hq.le] at h2
    have : (ε * x) ^ q - ε * x = (ε ^ q - ε) * x ^ q + ε * (x ^ q - x) := by ring
    rw [this]
    exact dvd_add (h2.mul_right _) h1
  let s : ℕ → O := fun n => (ε * x) ^ q ^ n
  have hsS : ∀ n, s (n + 1) = s n ^ q := fun n => by
    show (ε * x) ^ q ^ (n + 1) = ((ε * x) ^ q ^ n) ^ q
    rw [pow_succ q n, pow_mul (ε * x)]
  have hsd : ∀ n, ∃ y, s (n + 1) - s n = (V.l : O) ^ n * y := fun n => by
    have h1 := dvd_sub_pow_of_dvd_sub hz (d * n)
    have h2 : n ≤ d * n + 1 :=
      (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero (NeZero.ne d))).trans (Nat.le_succ _)
    have h3 := (pow_dvd_pow (V.l : O) h2).trans h1
    rw [pow_mul, ← hqdef, ← pow_mul, ← pow_succ'] at h3
    exact h3
  have hlim : ∀ a, ∃ z, ∀ n : ℕ, V.Ge n (z - em a (s n)) := fun a => by
    refine hcomp (fun n => em a (s n)) fun n => ?_
    obtain ⟨y, hy⟩ := hsd n
    show V.Ge n (em a (s (n + 1)) - em a (s n))
    rw [← map_sub, hy, map_mul, map_pow, map_natCast, mul_comm]
    exact (hint a y).mul_int (ge_l_pow V n)
  choose ζ hζ using hlim
  have hζint : ∀ a, V.Ge 0 (ζ a) := fun a => by
    have := (hζ a 0).add (by simpa using hint a (s 0))
    simpa using this
  let Z : ZMod d → intRing V := fun a => ⟨ζ a, hζint a⟩
  have hZ : ∀ a, π (Z a) = φ a x := fun a => by
    have h1 : π (Z a) = φ a (s 1) :=
      (hπ (Z a) (e a (s 1))).2 (mm_of_ge_one V (by have := hζ a 1; rw [Nat.cast_one] at this; exact this))
    rw [h1, hsS, map_pow, hper]
    simp [s, hφε]
  have hζq : ∀ a, ζ a ^ q = ζ a := fun a => by
    rw [← sub_eq_zero]
    refine eq_zero_of_ge V fun n => ?_
    have h1 := ge_pow_sub V (hζint a) (hint a (s n)) (hζ a n) q
    have h2 := (hζ a (n + 1)).mono (w' := n) (by push_cast; linarith)
    rw [hsS, map_pow] at h2
    have := h1.sub h2
    simpa using this
  have hζN : ∀ a, ζ a ^ (q - 1) = 1 := fun a => by
    have h0 : ζ a ≠ 0 := fun h => hx0 a (by
      rw [← hZ, show Z a = 0 from Subtype.ext h, map_zero])
    apply mul_right_cancel₀ h0
    rw [← pow_succ, Nat.sub_add_cancel hq.le, hζq, one_mul]
  have hl0 : (V.l : intRing V ⧸ maxId V) = 0 := by
    rw [← map_natCast π, ← map_zero π, hπ]
    simpa using mm_of_ge_one V VF.ge_l
  have hN : ((q - 1 : ℕ) : intRing V ⧸ maxId V) ≠ 0 := by
    rw [Nat.cast_sub hq.le, hqdef, Nat.cast_pow, hl0, zero_pow (NeZero.ne d)]
    simp
  refine ⟨q - 1, ζ, s, ?_, hζN, ?_, ?_, hsd, ?_⟩
  · refine le_antisymm (not_lt.1 fun h => hN ?_) (VF.ge_natCast (V := V) (q - 1))
    rw [← map_natCast π, ← map_zero π, hπ]
    simpa [VF.MM] using h
  · intro a a' h
    apply hxinj
    show φ a x = φ a' x
    rw [← hZ, ← hZ, show Z a = Z a' from Subtype.ext h]
  · intro a
    have hZN : ∀ a, Z a ^ (q - 1) = 1 := fun a => Subtype.ext (hζN a)
    have := root_eq π hN (hZN (a + 1)) (u := Z (a + 1)) (w := Z a ^ V.l)
      (by rw [← pow_mul, mul_comm, pow_mul, hZN, one_pow])
      (by rw [map_pow, hZ, hZ, hφ])
    exact congrArg Subtype.val this
  · intro a K
    exact ⟨K, fun n hn => (hζ a n).mono (by exact_mod_cast hn)⟩

end GlobalTheory
