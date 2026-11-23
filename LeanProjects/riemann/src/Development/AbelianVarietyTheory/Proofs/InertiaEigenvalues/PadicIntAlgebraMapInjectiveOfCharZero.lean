import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin

open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr

theorem padicInt_algebraMap_injective_of_charZero {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O]
    [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (algebraMap ℤ_[l] O (PadicInt.unitCoeff hx0 : ℤ_[l])) :=
    (PadicInt.unitCoeff hx0).isUnit.map _
  have hp : (l : O) ^ x.valuation = 0 := (mul_eq_zero.1 hx).resolve_left hu.ne_zero
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) (pow_eq_zero_iff'.1 hp).1

theorem exists_eq_X_pow_mul_of_ne_zero {O : Type} [CommRing O] {a : O⟦X⟧} (ha : a ≠ 0) :
    ∃ (m : ℕ) (w : O⟦X⟧), a = X ^ m * w ∧ constantCoeff w ≠ 0 := by
  refine ⟨a.order.toNat, a.divXPowOrder, X_pow_order_mul_divXPowOrder.symm, ?_⟩
  rw [constantCoeff_divXPowOrder]
  exact coeff_order ha

theorem X_pow_card_dvd_of_invariant {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] [Algebra ℤ_[l] O] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ] (a : O⟦X⟧)
    (h0 : constantCoeff a = 0) (ha : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a) :
    (X : O⟦X⟧) ^ Nat.card Δ ∣ a := by
  by_cases ha0 : a = 0
  · rw [ha0]
    exact dvd_zero _
  obtain ⟨m, w, rfl, hw⟩ := exists_eq_X_pow_mul_of_ne_zero ha0
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp only [pow_zero, one_mul] at h0
      exact absurd h0 hw
    · exact h
  have hpow : ∀ δ ∈ Δ, (δ : ℤ_[l]) ^ m = 1 := by
    intro δ hδ
    obtain ⟨v, hv, hv0⟩ := exists_act_X (O := O) (δ : ℤ_[l])
    have e := ha δ hδ
    rw [map_mul, map_pow, hv, mul_pow, mul_assoc] at e
    have e' := mul_left_cancel₀ (pow_ne_zero m X_ne_zero) e
    have e'' := congrArg constantCoeff e'
    rw [map_mul, map_pow, hv0, constantCoeff_act] at e''
    have h1 : (algebraMap ℤ_[l] O (δ : ℤ_[l])) ^ m = 1 := by
      have h2 : ((algebraMap ℤ_[l] O (δ : ℤ_[l])) ^ m - 1) * constantCoeff w = 0 := by
        rw [sub_mul, one_mul, e'', sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hw)
    apply padicInt_algebraMap_injective_of_charZero O
    rw [map_pow, h1, map_one]
  have hexp : Monoid.exponent Δ ∣ m := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
    apply Subtype.ext
    apply Units.ext
    simp [hpow g g.2]
  rw [IsCyclic.exponent_eq_card] at hexp
  exact (pow_dvd_pow X (Nat.le_of_dvd hm hexp)).trans (dvd_mul_right _ _)

theorem X_pow_dvd_mk_sub_sum {O : Type} [CommRing O] (c : ℕ → O) (N : ℕ) :
    (X : O⟦X⟧) ^ N ∣ PowerSeries.mk c - ∑ k ∈ Finset.range N, C (c k) * X ^ k := by
  rw [X_pow_dvd_iff]
  intro m hm
  simp [map_sum, hm]

theorem injective_and_range_eq_invariants {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (Δ : Subgroup ℤ_[l]ˣ) [Finite Δ]
    (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (hj : Associated (j X) (X ^ Nat.card Δ))
    (hinv : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) (j X) = j X) :
    Function.Injective j ∧
      ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ Δ, act O (δ : ℤ_[l]) a = a := by
  have hd : 0 < Nat.card Δ := Nat.card_pos
  obtain ⟨u, hu⟩ := hj
  have hjX0 : j X ≠ 0 := by
    intro h
    rw [h, zero_mul] at hu
    exact pow_ne_zero _ X_ne_zero hu.symm
  have hXj : (X : O⟦X⟧) ∣ j X := by
    have e : j X = X ^ Nat.card Δ * ((u⁻¹ : O⟦X⟧ˣ) : O⟦X⟧) := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e]
    exact (dvd_pow_self (X : O⟦X⟧) hd.ne').mul_right _
  have hinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    obtain ⟨m, w, rfl, hw⟩ := exists_eq_X_pow_mul_of_ne_zero hb0
    rw [map_mul, map_pow] at hb
    rcases mul_eq_zero.1 hb with h | h
    · exact pow_ne_zero m hjX0 h
    · apply hw
      rw [← constantCoeff_algHom j hXj w, h, map_zero]
  have hact : ∀ δ ∈ Δ, (act O (δ : ℤ_[l])).comp j = j := fun δ hδ =>
    algHom_ext_X _ _ (by rw [AlgHom.comp_apply, hinv δ hδ]; exact hXj)
      (by rw [AlgHom.comp_apply, hinv δ hδ])
  have hstep : ∀ q : O⟦X⟧, (∀ δ ∈ Δ, act O (δ : ℤ_[l]) q = q) →
      ∃ q' : O⟦X⟧, (∀ δ ∈ Δ, act O (δ : ℤ_[l]) q' = q') ∧
        q = C (constantCoeff q) + j X * q' := by
    intro q hq
    have h0 : constantCoeff (q - C (constantCoeff q)) = 0 := by simp
    have hi : ∀ δ ∈ Δ, act O (δ : ℤ_[l]) (q - C (constantCoeff q)) = q - C (constantCoeff q) := by
      intro δ hδ
      rw [map_sub, hq δ hδ, act_C]
    obtain ⟨r, hr⟩ := X_pow_card_dvd_of_invariant Δ _ h0 hi
    have hq' : q - C (constantCoeff q) = j X * (↑u * r) := by rw [hr, ← mul_assoc, hu]
    refine ⟨↑u * r, fun δ hδ => ?_, by rw [← hq']; ring⟩
    apply mul_left_cancel₀ hjX0
    rw [← hq', ← hinv δ hδ, ← map_mul, ← hq', hi δ hδ]
  choose f hf1 hf2 using hstep
  refine ⟨hinj, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨b, rfl⟩ δ hδ
    exact DFunLike.congr_fun (hact δ hδ) b
  · intro ha
    let S := {q : O⟦X⟧ // ∀ δ ∈ Δ, act O (δ : ℤ_[l]) q = q}
    let nxt : S → S := fun q => ⟨f q.1 q.2, hf1 q.1 q.2⟩
    let sq : ℕ → S := fun n => nxt^[n] ⟨a, ha⟩
    let c : ℕ → O := fun k => constantCoeff (sq k).1
    have hexp : ∀ N, a = ∑ k ∈ Finset.range N, C (c k) * j X ^ k + j X ^ N * (sq N).1 := by
      intro N
      induction N with
      | zero => simp [sq]
      | succ N ih =>
        have e1 : (sq (N + 1)).1 = f (sq N).1 (sq N).2 := by
          simp only [sq, Function.iterate_succ_apply']
          rfl
        have e2 : (sq N).1 = C (c N) + j X * (sq (N + 1)).1 := by
          rw [e1]
          exact hf2 _ _
        calc a = ∑ k ∈ Finset.range N, C (c k) * j X ^ k + j X ^ N * (sq N).1 := ih
          _ = ∑ k ∈ Finset.range N, C (c k) * j X ^ k +
              j X ^ N * (C (c N) + j X * (sq (N + 1)).1) := by rw [← e2]
          _ = _ := by rw [Finset.sum_range_succ]; ring
    have hjsum : ∀ N, j (∑ k ∈ Finset.range N, C (c k) * X ^ k) =
        ∑ k ∈ Finset.range N, C (c k) * j X ^ k := by
      intro N
      simp [map_sum, algHom_C]
    have hdvd : ∀ N, (X : O⟦X⟧) ^ N ∣ j (PowerSeries.mk c) - a := by
      intro N
      obtain ⟨r, hr⟩ := X_pow_dvd_mk_sub_sum c N
      have e3 : PowerSeries.mk c = ∑ k ∈ Finset.range N, C (c k) * X ^ k + X ^ N * r := by
        rw [← hr]
        ring
      have e4 : j (PowerSeries.mk c) - a = j X ^ N * (j r - (sq N).1) := by
        conv_lhs => rw [e3, map_add, map_mul, map_pow, hjsum, hexp N]
        ring
      rw [e4]
      exact (pow_dvd_pow_of_dvd hXj N).trans (dvd_mul_right _ _)
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    have h' := (X_pow_dvd_iff.1 (hdvd (n + 1))) n (Nat.lt_succ_self n)
    rw [map_sub, sub_eq_zero] at h'
    exact h'

end GlobalTheory.CycFr
