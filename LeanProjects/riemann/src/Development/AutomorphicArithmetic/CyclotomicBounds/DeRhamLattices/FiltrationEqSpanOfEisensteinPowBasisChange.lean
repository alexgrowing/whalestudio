import Mathlib

theorem _root_.UpperTheory.KN.filtration_eq_span_of_eisensteinPow_basisChange :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)), (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) → ∀ (eD : R), Function.Bijective (act eD) → ∀ (F : ℤ → W → Prop), (∀ (y : W) (j : ℤ), F j y ↔ F (j + 1) (act eD y)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (β : ℕ) (h b : ι → W) (m m' : Matrix ι ι R), m' * m = 1 → (∀ i, h i = ∑ k, act (eD ^ β * m i k) (b k)) → (∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ k, act (d k) (b k)) → ∀ w, F (β : ℤ) w ↔ ∃ d : ι → R, w = ∑ i, act (d i) (h i) := by
  intro R W _ _ act hmul hone eD hbij F hF ι _ _ β h b m m' hm hh hF0 w
  have hpow : ∀ (n : ℕ) (y : W), act (eD ^ n) y = (act eD)^[n] y := by
    intro n
    induction n with
    | zero => intro y; simp [hone]
    | succ n ih =>
      intro y
      rw [pow_succ, hmul, ih, Function.iterate_succ_apply]
  have hFn : ∀ (n : ℕ) (y : W), F 0 y ↔ F n ((act eD)^[n] y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [ih, hF, Function.iterate_succ_apply', Nat.cast_succ]
  have hinj : Function.Injective (act (eD ^ β)) := by
    intro x y hxy
    rw [hpow, hpow] at hxy
    exact (hbij.iterate β).1 hxy
  have hexp : ∀ d : ι → R,
      ∑ i, act (d i) (h i) = act (eD ^ β) (∑ k, act (∑ i, d i * m i k) (b k)) := by
    intro d
    simp only [hh, map_sum, AddMonoidHom.finset_sum_apply, ← hmul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
    exact congrArg (fun r => act r (b k)) (by ring)
  have hspan : ∀ y : W, (∃ d : ι → R, y = ∑ k, act (d k) (b k)) ↔
      ∃ e : ι → R, y = ∑ k, act (∑ i, e i * m i k) (b k) := by
    intro y
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨fun i => ∑ j, d j * m' j i, ?_⟩
      have hc : ∀ k, ∑ i, (∑ j, d j * m' j i) * m i k = d k := by
        intro k
        calc ∑ i, (∑ j, d j * m' j i) * m i k = ∑ j, d j * (m' * m) j k := by
              simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
              rw [Finset.sum_comm]
          _ = d k := by simp [hm, Matrix.one_apply]
      simp only [hc]
    · rintro ⟨e, rfl⟩
      exact ⟨fun k => ∑ i, e i * m i k, rfl⟩
  obtain ⟨y, rfl⟩ := (hbij.iterate β).2 w
  rw [← hFn β y, hF0, hspan, ← hpow]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [hexp, he]⟩
  · rintro ⟨e, he⟩
    exact ⟨e, hinj (by rw [he, hexp])⟩
