import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem powadd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal) (x y z : C), v x ≤ 1 → v y ≤ 1 → v (z - x - y) ≤ v (p : C) → v (z ^ p - x ^ p - y ^ p) ≤ v (p : C) := by
  intro p hp C _ v x y z hx hy h
  have hp1 : v (p : C) ≤ 1 := by
    exact natCast_mem v.integer p
  have hz : v z ≤ 1 := by
    have e : z = (z - x - y) + x + y := by ring
    rw [e]
    exact v.map_add_le (v.map_add_le (h.trans hp1) hx) hy
  let X : v.integer := ⟨x, hx⟩
  let Y : v.integer := ⟨y, hy⟩
  let Z : v.integer := ⟨z, hz⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out X Y
  obtain ⟨s, hs⟩ := sub_dvd_pow_sub_pow Z (X + Y) p
  have hr' := congrArg v.integer.subtype hr
  have hs' := congrArg v.integer.subtype hs
  simp only [map_add, map_mul, map_pow, map_sub, map_natCast, Subring.subtype_apply, X, Y, Z]
    at hr' hs'
  have e : z ^ p - x ^ p - y ^ p = (z - x - y) * (s : C) + (p : C) * (x * y * (r : C)) := by
    linear_combination hr' + hs'
  rw [e]
  refine v.map_add_le ?_ ?_
  · rw [map_mul]
    exact (mul_le_of_le_one_right' s.2).trans h
  · rw [map_mul]
    refine mul_le_of_le_one_right' ?_
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' hx hy) r.2

section

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem mem_pInt [CharZero C] (hv : v.Integers R) {p : ℕ} (hp : p ≠ 0) (x : C) :
    x ∈ pInt (C := C) R p ↔ v x ≤ v (p : C) := by
  have h0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [pInt, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left' (hv.map_le_one r)
  · intro h
    have h1 : v (x / p) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le
    obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
    exact ⟨r, by rw [Algebra.smul_def, hr, div_mul_cancel₀ _ h0]⟩

theorem val_le_one (hv : v.Integers R) {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {g : N → C} (hg : g ∈ AA.carrier) (x : N) : v (g x) ≤ 1 := by
  obtain ⟨r, hr⟩ := AA.le_int hg x
  rw [← hr]
  exact hv.map_le_one r

theorem pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {g : N → C} (hg : g ∈ AA.carrier) (k : ℕ) :
    g ^ k ∈ AA.carrier := by
  induction k with
  | zero => rw [pow_zero]; exact AA.one_mem
  | succ k ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg

theorem pow_congr (p : ℕ) [hp : Fact p.Prime] {x z : C} (hx : v x ≤ 1)
    (h : v (z - x) ≤ v (p : C)) : v (z ^ p - x ^ p) ≤ v (p : C) := by
  have := powadd p C v x 0 z hx (by simp) (by simpa using h)
  simpa [zero_pow hp.out.ne_zero] using this

end

theorem a_pow : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) := by
  intro p hp C _ _ _ v R _ _ hv hp1 F _ _ _ _ f hF N _ _ _ _ AA hst K t τ c hc
  obtain ⟨g, ⟨hg, hadd⟩, h1, h2, h3⟩ := hc
  have hp0 := hp.out.ne_zero
  have hb := val_le_one hv AA hg
  refine ⟨g ^ p, ⟨pow_mem AA hg p, fun x y => ?_⟩, fun a x => ?_, fun k hk => ?_, ?_⟩
  · rw [mem_pInt hv hp0]
    exact powadd p C v _ _ _ (hb x) (hb y) ((mem_pInt hv hp0 _).1 (hadd x y))
  · rw [mem_pInt hv hp0, MulChar.pow_apply' _ hp0, map_pow, Pi.pow_apply, Pi.pow_apply, ← mul_pow]
    refine pow_congr p ?_ ((mem_pInt hv hp0 _).1 (h1 a x))
    rw [map_mul]
    exact mul_le_one' (hv.map_le_one _) (hb x)
  · rw [mem_pInt hv hp0]
    have := pow_congr (v := v) p (x := 0) (z := g k) (by simp)
      (by simpa using (mem_pInt hv hp0 _).1 (h2 k hk))
    simpa [zero_pow hp0] using this
  · rw [mem_pInt hv hp0, map_pow, Pi.pow_apply]
    exact pow_congr p (hv.map_le_one _) ((mem_pInt hv hp0 _).1 h3)

end PositivityTheory.HtPt.Rd
