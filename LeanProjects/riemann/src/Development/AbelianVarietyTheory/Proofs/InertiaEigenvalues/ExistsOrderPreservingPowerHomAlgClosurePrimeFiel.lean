import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.PowAut

theorem exists_coprime_lift (N k a : ℕ) (hN : 0 < N) (hk : 0 < k) (ha : a.Coprime N) :
    ∃ b : ℕ, b.Coprime (N * k) ∧ b ≡ a [MOD N] := by
  haveI : NeZero (N * k) := ⟨(Nat.mul_pos hN hk).ne'⟩
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (Dvd.intro k rfl : N ∣ N * k)
    (ZMod.unitOfCoprime a ha)
  refine ⟨(u : ZMod (N * k)).val, ZMod.val_coe_unit_coprime u, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have h := congrArg (fun v : (ZMod N)ˣ => (v : ZMod N)) hu
  simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply,
    ZMod.coe_unitOfCoprime] at h
  rw [← h, ZMod.natCast_val]

theorem exists_exponents (M n : ℕ) (hM : 0 < M) (hn : n.Coprime M) :
    ∃ a : ℕ → ℕ, a 0 = n ∧ (∀ j, (a j).Coprime (M * j.factorial)) ∧
      ∀ i j, i ≤ j → a j ≡ a i [MOD M * i.factorial] := by
  have step : ∀ j : ℕ, ∀ a : {a : ℕ // a.Coprime (M * j.factorial)},
      ∃ b : {b : ℕ // b.Coprime (M * (j + 1).factorial)}, b.1 ≡ a.1 [MOD M * j.factorial] := by
    intro j a
    obtain ⟨b, hb, hb'⟩ := exists_coprime_lift (M * j.factorial) (j + 1) a.1
      (Nat.mul_pos hM j.factorial_pos) j.succ_pos a.2
    refine ⟨⟨b, ?_⟩, hb'⟩
    rw [Nat.factorial_succ, mul_comm (j + 1), ← mul_assoc]
    exact hb
  choose f hf using step
  let s : ∀ j : ℕ, {a : ℕ // a.Coprime (M * j.factorial)} := fun j =>
    Nat.rec (motive := fun j => {a : ℕ // a.Coprime (M * j.factorial)})
      ⟨n, by simpa using hn⟩ f j
  have hs : ∀ j, s (j + 1) = f j (s j) := fun j => rfl
  refine ⟨fun j => (s j).1, rfl, fun j => (s j).2, ?_⟩
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact Nat.ModEq.refl _
  | succ j hij ih =>
    have h1 : (s (j + 1)).1 ≡ (s j).1 [MOD M * j.factorial] := by rw [hs]; exact hf j (s j)
    exact (h1.of_dvd (Nat.mul_dvd_mul_left M (Nat.factorial_dvd_factorial hij))).trans ih

theorem orderOf_pos_of_ne_zero (g : ℕ) [Fact g.Prime] (x : AlgebraicClosure (ZMod g))
    (hx : x ≠ 0) : 0 < orderOf x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  haveI := Fintype.ofFinite (IntermediateField.adjoin (ZMod g) {x})
  let y : IntermediateField.adjoin (ZMod g) {x} :=
    ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy
  have h2 : x ^ (Fintype.card (IntermediateField.adjoin (ZMod g) {x}) - 1) = 1 :=
    congrArg Subtype.val h1
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨_, Nat.sub_pos_of_lt Fintype.one_lt_card, h2⟩)

theorem exists_powHom {K : Type*} [Field K] (hK : ∀ x : K, x ≠ 0 → 0 < orderOf x)
    (M n : ℕ) (hM : 0 < M) (hn : n.Coprime M) :
    ∃ θ : K →* K, Function.Injective θ ∧ (∀ x, orderOf (θ x) = orderOf x) ∧
      ∀ x, x ^ M = 1 → θ x = x ^ n := by
  classical
  obtain ⟨a, ha0, hac, ha⟩ := exists_exponents M n hM hn
  let t : K → K := fun x => if x = 0 then 0 else x ^ a (orderOf x)
  have t0 : t 0 = 0 := if_pos rfl
  have ht : ∀ x : K, x ≠ 0 → ∀ j, orderOf x ≤ j → t x = x ^ a j := by
    intro x hx j hj
    have : t x = x ^ a (orderOf x) := if_neg hx
    rw [this]
    have h := (ha _ _ hj).of_dvd
      (Dvd.dvd.mul_left (Nat.dvd_factorial (hK x hx) le_rfl) M)
    rw [← pow_mod_orderOf x (a j), ← pow_mod_orderOf x (a (orderOf x)), h]
  let θ : K →* K :=
    { toFun := t
      map_one' := by rw [ht 1 one_ne_zero _ le_rfl, one_pow]
      map_mul' := by
        intro x y
        by_cases hx : x = 0
        · rw [hx, zero_mul, t0, zero_mul]
        by_cases hy : y = 0
        · rw [hy, mul_zero, t0, mul_zero]
        rw [ht x hx (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          ht y hy (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          ht _ (mul_ne_zero hx hy) (orderOf x + orderOf y + orderOf (x * y)) (by omega),
          mul_pow] }
  have hθ : ∀ x, θ x = t x := fun _ => rfl
  have hord : ∀ x, orderOf (θ x) = orderOf x := by
    intro x
    by_cases hx : x = 0
    · rw [hθ, hx, t0]
    rw [hθ, ht x hx _ le_rfl]
    exact Nat.Coprime.orderOf_pow ((hac (orderOf x)).coprime_dvd_right
      (Dvd.dvd.mul_left (Nat.dvd_factorial (hK x hx) le_rfl) M)).symm
  have hne : ∀ x : K, x ≠ 0 → θ x ≠ 0 := by
    intro x hx
    rw [hθ, ht x hx _ le_rfl]
    exact pow_ne_zero _ hx
  refine ⟨θ, ?_, hord, ?_⟩
  · intro x y hxy
    by_cases hy : y = 0
    · by_contra h
      exact hne x (hy ▸ h) (by rw [hxy, hy, hθ, t0])
    have h1 : θ (x * y⁻¹) * θ y = 1 * θ y := by
      rw [← map_mul, inv_mul_cancel_right₀ hy, one_mul, hxy]
    have h2 := mul_right_cancel₀ (hne y hy) h1
    have h3 : orderOf (x * y⁻¹) = 1 := by rw [← hord, h2, orderOf_one]
    rw [orderOf_eq_one_iff, mul_inv_eq_one₀ hy] at h3
    exact h3
  · intro x hxM
    have hx : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne'] at hxM
      exact zero_ne_one hxM
    have h := (ha 0 (orderOf x) (Nat.zero_le _)).of_dvd
      (Dvd.dvd.mul_right (orderOf_dvd_of_pow_eq_one hxM) _)
    rw [hθ, ht x hx _ le_rfl, ← ha0, ← pow_mod_orderOf x (a 0),
      ← pow_mod_orderOf x (a (orderOf x)), h]

theorem exists_powHom_fbar : ∀ (g : ℕ) [Fact g.Prime] (M n : ℕ), 0 < M → n.Coprime M →
    ∃ θ : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar g, Function.Injective θ ∧
      (∀ x, orderOf (θ x) = orderOf x) ∧ ∀ x, x ^ M = 1 → θ x = x ^ n :=
  fun g _ M n hM hn => exists_powHom (orderOf_pos_of_ne_zero g) M n hM hn

end GlobalTheory.PowAut
