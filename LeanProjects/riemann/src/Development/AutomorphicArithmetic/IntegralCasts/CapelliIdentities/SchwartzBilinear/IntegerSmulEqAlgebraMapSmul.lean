import Mathlib

namespace UpperTheory.Reformulated.B.P6.r03a

theorem integer_smul_eq_algebraMap_smul {K : Type} [Field K] [NumberField K] {n : ℕ}
    (r : NumberField.RingOfIntegers K) (x : Fin n → K) :
    r • x = (algebraMap (NumberField.RingOfIntegers K) K r) • x :=
  (algebraMap_smul K r x).symm

theorem GlobalTheory.CompanionTheory.Adelic.SatLine.exists_smul_mem :
    ∀ {K : Type} [inst : Field K] [NumberField K] {n : ℕ} (M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)) {x : Fin n → K}, x ∈ Submodule.span K (SetLike.coe M) → ∃ (c : NumberField.RingOfIntegers K), c ≠ OfNat.ofNat (nat_lit 0) ∧ c • x ∈ M := by
  intro K _ _ n M x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨c1, hc1, h1⟩ := hy
    obtain ⟨c2, hc2, h2⟩ := hz
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    have e : (c1 * c2) • (y + z) = c2 • (c1 • y) + c1 • (c2 • z) := by
      rw [smul_add, mul_smul c1 c2 z, mul_comm c1 c2, mul_smul c2 c1 y]
    rw [e]
    exact M.add_mem (M.smul_mem c2 h1) (M.smul_mem c1 h2)
  | smul a y _ hy =>
    obtain ⟨c, hc, h⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    refine ⟨(q : NumberField.RingOfIntegers K) * c, mul_ne_zero (nonZeroDivisors.ne_zero q.2) hc, ?_⟩
    have hpq' : a * algebraMap (NumberField.RingOfIntegers K) K (q : NumberField.RingOfIntegers K)
        = algebraMap (NumberField.RingOfIntegers K) K p := hpq
    have e : ((q : NumberField.RingOfIntegers K) * c) • (a • y) = p • (c • y) := by
      rw [integer_smul_eq_algebraMap_smul ((q : NumberField.RingOfIntegers K) * c) (a • y), integer_smul_eq_algebraMap_smul p (c • y),
        integer_smul_eq_algebraMap_smul c y, smul_smul, smul_smul, map_mul, ← hpq']
      congr 1
      ring
    rw [e]
    exact M.smul_mem p h

end UpperTheory.Reformulated.B.P6.r03a
