import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open Polynomial

namespace GlobalTheory.GLq.LabelModel
theorem lift {F : Type} [Field F] {m M : ℕ} (hM : 0 < M) (hm : m ∣ M) {ξ ζ : F} (hξ : IsPrimitiveRoot ξ M)
    (hζ : IsPrimitiveRoot ζ m) : ∃ ξ' : F, IsPrimitiveRoot ξ' M ∧ ξ' ^ (M / m) = ζ := by
  obtain ⟨c, rfl⟩ := hm
  have hm0 : 0 < m := Nat.pos_of_mul_pos_right hM
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero (m * c) := ⟨hM.ne'⟩
  have hη : IsPrimitiveRoot (ξ ^ c) m := hξ.pow hM (mul_comm _ _)
  obtain ⟨a, -, hac, ha⟩ := (hη.isPrimitiveRoot_iff).1 hζ
  obtain ⟨U, hU⟩ := ZMod.unitsMap_surjective (n := m) (m := m * c) (Dvd.intro _ rfl) (ZMod.unitOfCoprime a hac)
  refine ⟨ξ ^ (U : ZMod (m * c)).val, hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime U), ?_⟩
  rw [Nat.mul_div_cancel_left _ hm0, ← pow_mul, mul_comm, pow_mul, ← ha]
  have h1 : (((U : ZMod (m * c)).val : ℕ) : ZMod m) = (a : ZMod m) := by
    have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hU
    simpa [ZMod.unitsMap_val] using this
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  rw [pow_eq_pow_mod _ hη.pow_eq_one, pow_eq_pow_mod a hη.pow_eq_one, h2]

variable (g : ℕ) [hg : Fact g.Prime]

theorem pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hg.out.one_lt)

theorem dv {d e : ℕ} (h : d ∣ e) : g ^ d - 1 ∣ g ^ e - 1 := Nat.pow_sub_one_dvd_pow_sub_one g h

theorem exprim {d : ℕ} (hd : 0 < d) : ∃ ξ : Formalism.CyclotomicNorms.Fbar g, IsPrimitiveRoot ξ (g ^ d - 1) := by
  haveI : NeZero (((g ^ d - 1 : ℕ)) : Formalism.CyclotomicNorms.Fbar g) := ⟨by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hg.out.pos), Nat.cast_pow, CharP.cast_eq_zero (Formalism.CyclotomicNorms.Fbar g) g, zero_pow hd.ne']
    simp⟩
  haveI : NeZero (g ^ d - 1) := ⟨(pos g hd).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ _

theorem chain : ∃ z : ℕ → Formalism.CyclotomicNorms.Fbar g, ∀ n, IsPrimitiveRoot (z n) (g ^ n.factorial - 1) ∧
    z (n+1) ^ ((g ^ (n+1).factorial - 1) / (g ^ n.factorial - 1)) = z n := by
  have step : ∀ n (x : {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ n.factorial - 1)}),
      ∃ y : {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ (n+1).factorial - 1)},
        y.1 ^ ((g ^ (n+1).factorial - 1) / (g ^ n.factorial - 1)) = x.1 := by
    intro n x
    obtain ⟨ξ, hξ⟩ := exprim g (Nat.factorial_pos (n+1))
    obtain ⟨y, hy, hy'⟩ := lift (pos g (Nat.factorial_pos (n+1))) (dv g (Nat.factorial_dvd_factorial (Nat.le_succ n))) hξ x.2
    exact ⟨⟨y, hy⟩, hy'⟩
  choose f hf using step
  obtain ⟨x0, hx0⟩ := exprim g (Nat.factorial_pos 0)
  let s : ∀ n : ℕ, {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ n.factorial - 1)} :=
    fun n => Nat.rec ⟨x0, hx0⟩ (fun n x => f n x) n
  exact ⟨fun n => (s n).1, fun n => ⟨(s n).2, hf n (s n)⟩⟩

theorem divmul {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (hb : 0 < b) : c / b * (b / a) = c / a := by
  obtain ⟨u, rfl⟩ := h1
  obtain ⟨v, rfl⟩ := h2
  have ha : 0 < a := Nat.pos_of_mul_pos_right hb
  rw [Nat.mul_div_cancel_left _ hb, Nat.mul_div_cancel_left _ ha, mul_assoc, Nat.mul_div_cancel_left _ ha, mul_comm]

theorem gensys : ∃ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, ∀ d, 0 < d → IsPrimitiveRoot (ζ d) (g ^ d - 1) ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = ζ d := by
  obtain ⟨z, hz⟩ := chain g
  have hc : ∀ n k, z (n + k) ^ ((g ^ (n+k).factorial - 1) / (g ^ n.factorial - 1)) = z n := by
    intro n k
    induction k with
    | zero => simp [Nat.div_self (pos g (Nat.factorial_pos n))]
    | succ k ih =>
      rw [← ih, ← (hz (n+k)).2, ← pow_mul, ← add_assoc,
        divmul (dv g (Nat.factorial_dvd_factorial (Nat.le_add_right n k)))
          (dv g (Nat.factorial_dvd_factorial (Nat.le_succ _))) (pos g (Nat.factorial_pos _))]
  refine ⟨fun d => z d ^ ((g ^ d.factorial - 1) / (g ^ d - 1)), fun d hd => ⟨?_, fun d' hdd hd' => ?_⟩⟩
  · exact (hz d).1.pow (pos g (Nat.factorial_pos _)) (Nat.div_mul_cancel (dv g (Nat.dvd_factorial hd le_rfl))).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_dvd hd' hdd)
    beta_reduce
    rw [← hc d k, ← pow_mul, ← pow_mul,
      divmul (dv g hdd) (dv g (Nat.dvd_factorial hd' le_rfl)) (pos g hd'),
      divmul (dv g (Nat.dvd_factorial hd le_rfl)) (dv g (Nat.factorial_dvd_factorial (Nat.le_add_right d k))) (pos g (Nat.factorial_pos _))]

theorem level (x : Formalism.CyclotomicNorms.Fbar g) (hx : x ≠ 0) : ∃ d, 0 < d ∧ x ^ (g ^ d - 1) = 1 := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  let K := IntermediateField.adjoin (ZMod g) {x}
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = g ^ Module.finrank (ZMod g) K := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card]
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have := FiniteField.pow_card_sub_one_eq_one y hy
  rw [hcard] at this
  exact ⟨_, Module.finrank_pos, by simpa [y] using congrArg Subtype.val this⟩

noncomputable def E (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((g ^ d - 1 : ℕ) : ℂ))

theorem E_prim {d : ℕ} (hd : 0 < d) : IsPrimitiveRoot (E g d) (g ^ d - 1) :=
  Complex.isPrimitiveRoot_exp _ (pos g hd).ne'

theorem E_pow {d d' : ℕ} (h : d ∣ d') (hd : 0 < d) (hd' : 0 < d') : E g d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = E g d := by
  obtain ⟨c, hc⟩ := dv g h
  have h1 := pos g hd
  have h2 := pos g hd'
  have hc0 : c ≠ 0 := by rintro rfl; omega
  unfold E
  rw [← Complex.exp_nat_mul, hc, Nat.mul_div_cancel_left _ h1]
  congr 1
  have : ((g ^ d - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h1.ne'
  have : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc0
  rw [Nat.cast_mul]
  field_simp

theorem prim_iff {R : Type} [CommMonoid R] {z : R} {m : ℕ} (h : IsPrimitiveRoot z m) (hm : 0 < m) (a b : ℕ) :
    z ^ a = z ^ b ↔ a ≡ b [MOD m] := by
  have hf : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, h.pow_eq_one⟩
  rw [hf.pow_eq_pow_iff_modEq, ← h.eq_orderOf]

theorem inhab : Nonempty (LabelDatum g) := by
  classical
  obtain ⟨ζ, hζ⟩ := gensys g
  let R : Formalism.CyclotomicNorms.Fbar g → ℂ → Prop := fun x c => ∃ d, 0 < d ∧ ∃ j, x = ζ d ^ j ∧ c = E g d ^ j
  have common : ∀ x c y c', R x c → R y c' → ∃ d, 0 < d ∧ ∃ j j', x = ζ d ^ j ∧ c = E g d ^ j ∧ y = ζ d ^ j' ∧ c' = E g d ^ j' := by
    rintro x c y c' ⟨d, hd, j, rfl, rfl⟩ ⟨e, he, k, rfl, rfl⟩
    have hde := Nat.mul_pos hd he
    refine ⟨d * e, hde, (g ^ (d * e) - 1) / (g ^ d - 1) * j, (g ^ (d * e) - 1) / (g ^ e - 1) * k, ?_, ?_, ?_, ?_⟩
    · rw [pow_mul (ζ _), (hζ d hd).2 _ (Dvd.intro _ rfl) hde]
    · rw [pow_mul (E _ _), E_pow g (Dvd.intro _ rfl) hd hde]
    · rw [pow_mul (ζ _), (hζ e he).2 _ (Dvd.intro_left _ rfl) hde]
    · rw [pow_mul (E _ _), E_pow g (Dvd.intro_left _ rfl) he hde]
  have key : ∀ x c y c', R x c → R y c' → (x = y ↔ c = c') := by
    intro x c y c' h h'
    obtain ⟨d, hd, j, j', rfl, rfl, rfl, rfl⟩ := common _ _ _ _ h h'
    rw [prim_iff (hζ d hd).1 (pos g hd), prim_iff (E_prim g hd) (pos g hd)]
  have mul : ∀ x c y c', R x c → R y c' → R (x * y) (c * c') := by
    intro x c y c' h h'
    obtain ⟨d, hd, j, j', rfl, rfl, rfl, rfl⟩ := common _ _ _ _ h h'
    exact ⟨d, hd, j + j', (pow_add _ _ _).symm, (pow_add _ _ _).symm⟩
  have ex : ∀ x, x ≠ 0 → ∃ c, R x c := by
    intro x hx
    obtain ⟨d, hd, h⟩ := level g x hx
    haveI : NeZero (g ^ d - 1) := ⟨(pos g hd).ne'⟩
    obtain ⟨j, -, hj⟩ := (hζ d hd).1.eq_pow_of_pow_eq_one h
    exact ⟨_, d, hd, j, hj.symm, rfl⟩
  choose! t ht using ex
  let t' : Formalism.CyclotomicNorms.Fbar g → ℂ := fun x => if x = 0 then 0 else t x
  have ht' : ∀ x, x ≠ 0 → R x (t' x) := fun x hx => by simpa [t', hx] using ht x hx
  refine ⟨⟨⟨⟨t', ?_⟩, ?_⟩, ?_, ζ, fun d hd => (hζ d hd).1.eq_orderOf.symm,
    fun d e hd he => (hζ d hd).2 _ (Dvd.intro _ rfl) (Nat.mul_pos hd he)⟩⟩
  · exact (key _ _ _ _ (ht' 1 one_ne_zero) ⟨1, one_pos, 0, by simp, by simp⟩).1 rfl
  · intro x y
    by_cases hx : x = 0
    · simp [t', hx]
    by_cases hy : y = 0
    · simp [t', hy]
    exact (key _ _ _ _ (ht' _ (mul_ne_zero hx hy)) (mul _ _ _ _ (ht' x hx) (ht' y hy))).1 rfl
  · intro x y hx hy h
    exact (key _ _ _ _ (ht' x hx) (ht' y hy)).2 h

theorem inhab_teich (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) :
    ∃ L : LabelDatum g, L.teich = t := by
  obtain ⟨L⟩ := inhab g
  exact ⟨⟨t, ht, L.gen, L.gen_order, L.gen_norm⟩, rfl⟩

theorem thetaOf_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  have hp : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have h1 := (prim_iff hp (pos g hd) _ _).1 h.choose_spec
  have h2 : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [thetaOf, dif_pos h, pow_eq_pow_mod _ h2, pow_eq_pow_mod n h2, h1]

theorem isCusp_one (χ : Gn g 1 → ℂ) : IsCusp χ ↔ IsIrr χ :=
  ⟨fun h => h.2.1, fun h => ⟨one_pos, h, fun a h1 h2 => by omega⟩⟩

end GlobalTheory.GLq.LabelModel
