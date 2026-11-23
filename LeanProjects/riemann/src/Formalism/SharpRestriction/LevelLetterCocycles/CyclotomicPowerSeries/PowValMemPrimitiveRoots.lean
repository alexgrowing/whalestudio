import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstantCoeffAeval
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.EmultiplicityEqValuation

noncomputable section

namespace LevelStatements.Link

open PowerSeries

theorem pow_val_mem_primitiveRoots {LL : Type} [Field LL] (N : ℕ) (hN : 0 < N) (w : ZMod N)
    (hw : IsUnit w) {ξ : LL} (hξ : ξ ∈ primitiveRoots N LL) : ξ ^ w.val ∈ primitiveRoots N LL := by
  obtain ⟨u, rfl⟩ := hw
  rw [mem_primitiveRoots hN] at hξ ⊢
  exact hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime u)

theorem eq_of_pow_pred_eq_one {l : ℕ} [Fact l.Prime] (s : ℕ) (a b : ZMod (l ^ (s + 1)))
    (ha : a ^ (l - 1) = 1) (hb : b ^ (l - 1) = 1) (hab : (l : ZMod (l ^ (s + 1))) ∣ b - a) :
    b = a := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  set x := b - a with hx
  have hba : b = a + x := by rw [hx]; ring
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion
    (Polynomial.X ^ (l - 1) : Polynomial (ZMod (l ^ (s + 1)))) a x
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.derivative_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C] at hk
  rw [← hba, ha, hb] at hk
  have hlpow : (l : ZMod (l ^ (s + 1))) ^ (s + 1) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hxpow : x ^ (s + 1) = 0 := by
    obtain ⟨t, ht⟩ := hab
    rw [ht, mul_pow, hlpow, zero_mul]
  have hkx : IsNilpotent (k * x) := ⟨s + 1, by rw [mul_pow, hxpow, mul_zero]⟩
  have hl1 : IsUnit ((l - 1 : ℕ) : ZMod (l ^ (s + 1))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hinv : a * a ^ (l - 1 - 1) = 1 := by
    rw [← pow_succ', show l - 1 - 1 + 1 = l - 1 by omega, ha]
  have ha' : IsUnit a := ⟨⟨a, a ^ (l - 1 - 1), hinv, by rw [mul_comm]; exact hinv⟩, rfl⟩
  have hU : IsUnit (((l - 1 : ℕ) : ZMod (l ^ (s + 1))) * a ^ (l - 1 - 1) + k * x) :=
    hkx.isUnit_add_left_of_commute (hl1.mul (ha'.pow _)) (Commute.all _ _)
  have hx0 : x * (((l - 1 : ℕ) : ZMod (l ^ (s + 1))) * a ^ (l - 1 - 1) + k * x) = 0 := by
    linear_combination (-1 : ZMod (l ^ (s + 1))) * hk
  have hx' : x = 0 := hU.mul_left_eq_zero.mp hx0
  exact sub_eq_zero.mp hx'

theorem exists_toZModPow_eq_of_pow_pred_eq_one {l : ℕ} [Fact l.Prime] {Δ : Type*} (om : Δ → ℤ_[l])
    (hom : ∀ j, om j ^ (l - 1) = 1)
    (hom' : ∀ a : ZMod l, a ≠ 0 → ∃ j, PadicInt.toZMod (om j) = a) (s : ℕ)
    (a : ZMod (l ^ (s + 1))) (ha : a ^ (l - 1) = 1) :
    ∃ j, PadicInt.toZModPow (s + 1) (om j) = a := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  haveI : NeZero (l ^ (s + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hdvd : l ∣ l ^ (s + 1) := dvd_pow_self l (Nat.succ_ne_zero s)
  set π := ZMod.castHom hdvd (ZMod l) with hπ
  have hψ : π.comp (PadicInt.toZModPow (s + 1)) = (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    apply ZMod.ringHom_eq_of_ker_eq
    have m1 := RingHom.ker_isMaximal_of_surjective _
      (ZMod.ringHom_surjective (π.comp (PadicInt.toZModPow (s + 1))))
    have m2 := RingHom.ker_isMaximal_of_surjective _
      (ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[l] →+* ZMod l))
    rw [IsLocalRing.eq_maximalIdeal m1, IsLocalRing.eq_maximalIdeal m2]
  have key : ∀ y : ZMod (l ^ (s + 1)), π y = 0 → (l : ZMod (l ^ (s + 1))) ∣ y := by
    intro y hy
    rw [← ZMod.natCast_zmod_val y, map_natCast] at hy
    obtain ⟨t, ht⟩ := (CharP.cast_eq_zero_iff (ZMod l) l y.val).mp hy
    refine ⟨(t : ZMod (l ^ (s + 1))), ?_⟩
    rw [← ZMod.natCast_zmod_val y, ht, Nat.cast_mul]
  have ha0 : π a ≠ 0 := by
    intro h0
    have hpa : π a ^ (l - 1) = 1 := by rw [← map_pow, ha, map_one]
    rw [h0, zero_pow (by omega)] at hpa
    exact zero_ne_one hpa
  obtain ⟨j, hj⟩ := hom' (π a) ha0
  refine ⟨j, eq_of_pow_pred_eq_one s a _ ha ?_ ?_⟩
  · rw [← map_pow, hom j, map_one]
  · have hc : π (PadicInt.toZModPow (s + 1) (om j)) = PadicInt.toZMod (om j) :=
      RingHom.congr_fun hψ (om j)
    have hk : π (PadicInt.toZModPow (s + 1) (om j) - a) = 0 := by
      rw [map_sub, hc, hj, sub_self]
    exact key _ hk

theorem map_cyclotomic_comp {O LL : Type} [CommRing O] [Field LL] [CharZero LL] [Algebra O LL]
    (ρ : PowerSeries O →ₐ[O] PowerSeries LL) (ζ : LL) (hρ : 1 + ρ X = C ζ * exp LL) (m : ℕ) :
    ρ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
      Polynomial.aeval (C ζ * exp LL) (Polynomial.cyclotomic m LL) := by
  have key : ∀ p : Polynomial O, ρ (p : PowerSeries O) = Polynomial.aeval (ρ X) p := by
    intro p
    have h := Polynomial.algHom_ext (f := ρ.comp (Polynomial.coeToPowerSeries.algHom O))
      (g := Polynomial.aeval (ρ X)) (by simp)
    have hp := AlgHom.congr_fun h p
    simpa using hp
  rw [key, Polynomial.aeval_comp]
  have h1 : Polynomial.aeval (ρ X) (Polynomial.X + 1 : Polynomial O) = C ζ * exp LL := by
    rw [map_add, Polynomial.aeval_X, map_one, add_comm, hρ]
  rw [h1, ← Polynomial.map_cyclotomic m (algebraMap O LL), Polynomial.aeval_map_algebraMap]

end LevelStatements.Link
