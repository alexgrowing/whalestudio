import Mathlib

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isAdicComplete_of_pow_le_of_le {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] {I J : Ideal R} (hI : IsAdicComplete I M) {n : ℕ} (hJI : J ^ n ≤ I)
    (hIJ : I ≤ J) : IsAdicComplete J M := by
  have h1 : ∀ m : ℕ, (J ^ ((n + 1) * m) • ⊤ : Submodule R M) ≤ I ^ m • ⊤ := fun m => by
    apply Submodule.smul_mono_left
    rw [pow_mul]
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hJI) m
  have h2 : ∀ m : ℕ, (I ^ m • ⊤ : Submodule R M) ≤ J ^ m • ⊤ := fun m =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ m)
  have hH : IsHausdorff J M := ⟨fun x hx =>
    hI.toIsHausdorff.haus x fun m => (hx ((n + 1) * m)).mono (h1 m)⟩
  have hP : IsPrecomplete J M := ⟨fun f hf => by
    obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec (f := fun m => f ((n + 1) * m))
      (fun {a b} hab => (hf (Nat.mul_le_mul_left (n + 1) hab)).mono (h1 a))
    refine ⟨L, fun k => ?_⟩
    exact (hf (Nat.le_mul_of_pos_left k (Nat.succ_pos n))).trans ((hL k).mono (h2 k))⟩
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

theorem exists_pow_le_span_of_fg_of_integers {C : Type*} [Field C] {v : Valuation C NNReal}
    {O : Type*} [CommRing O] [Algebra O C] (hv : v.Integers O) {J : Ideal O} (hJ : J.FG)
    (hJ' : J ≠ ⊤) {a : O} (ha : v (algebraMap O C a) ≠ 0) :
    ∃ n : ℕ, J ^ n ≤ Ideal.span {a} := by
  classical
  obtain ⟨S, rfl⟩ := hJ
  set r : NNReal := S.sup fun s => v (algebraMap O C s) with hr
  have hr1 : r < 1 := by
    rw [hr, Finset.sup_lt_iff (by simp)]
    intro s hs
    refine lt_of_le_of_ne (hv.map_le_one s) fun h => hJ' ?_
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span hs) (hv.isUnit_of_one' h)
  have hS : ∀ x ∈ Ideal.span (S : Set O), v (algebraMap O C x) ≤ r := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Finset.le_sup (f := fun s => v (algebraMap O C s)) hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact v.map_add_le hx hy
    | smul c x _ hx =>
      rw [smul_eq_mul, map_mul, map_mul]
      exact (mul_le_of_le_one_left' (hv.map_le_one c)).trans hx
  have hpow : ∀ n : ℕ, ∀ x ∈ (Ideal.span (S : Set O)) ^ n, v (algebraMap O C x) ≤ r ^ n := by
    intro n
    induction n with
    | zero => intro x _; simpa using hv.map_le_one x
    | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z hy hz => ?_)
      · rw [map_mul, map_mul, pow_succ]
        exact mul_le_mul' (ih y hy) (hS z hz)
      · rw [map_add]; exact v.map_add_le hy hz
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one (pos_iff_ne_zero.mpr ha) hr1
  refine ⟨n, fun x hx => ?_⟩
  rw [Ideal.mem_span_singleton]
  exact hv.dvd_of_le ((hpow n x hx).trans hn.le)

theorem isAdicComplete_of_fg_of_natCast_mem : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (p : ℕ), p ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O → ∀ J : Ideal O, J.FG → J ≠ ⊤ → (p : O) ∈ J → IsAdicComplete J O := by
  intro C _ _ _ v O _ _ hv p hp hc J hJ hJ' hpJ
  have ha : v (algebraMap O C (p : O)) ≠ 0 := by
    rw [map_natCast, Ne, v.zero_iff]
    exact_mod_cast hp
  obtain ⟨n, hn⟩ := exists_pow_le_span_of_fg_of_integers hv hJ hJ' ha
  exact isAdicComplete_of_pow_le_of_le hc hn ((Ideal.span_singleton_le_iff_mem _).mpr hpJ)

end GlobalTheory
