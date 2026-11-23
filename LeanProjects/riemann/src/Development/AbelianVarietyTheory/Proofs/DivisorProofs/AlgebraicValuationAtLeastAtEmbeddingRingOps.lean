import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam.SzSum

section

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem sz_zero (r : ℝ) : Sz l lam r 0 := by
  refine ⟨zero_mem _, ?_⟩
  have : (⟨0, zero_mem _⟩ : algebraicClosure ℚ ℂ) = 0 := rfl
  rw [this, map_zero, norm_zero]
  positivity

theorem sz_add {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x + y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨add_mem hx hy, ?_⟩
  have : (⟨x + y, add_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hy')

theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

theorem sz_sub {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x - y) := by
  rw [sub_eq_add_neg]
  exact sz_add hx (sz_neg hy)

theorem sz_mul {r s : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam s y) : Sz l lam (r + s) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r s : ℝ} {x : ℂ} (h : r ≤ s) (hx : Sz l lam r x) : Sz l lam s x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

theorem sz_int (n : ℤ) : Sz l lam 0 (n : ℂ) := by
  refine ⟨intCast_mem _ n, ?_⟩
  have : (⟨(n : ℂ), intCast_mem _ n⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) := Subtype.ext (by simp)
  rw [this, map_intCast, Real.rpow_zero]
  exact IsUltrametricDist.norm_intCast_le_one _ n

theorem sz_sum {κ : Type*} (t : Finset κ) {r : ℝ} {x : κ → ℂ} (h : ∀ k ∈ t, Sz l lam r (x k)) :
    Sz l lam r (∑ k ∈ t, x k) :=
  Finset.sum_induction x (Sz l lam r) (fun _ _ => sz_add) (sz_zero r) h

end

theorem sz_ring : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ r : ℝ, Sz l lam r 0) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y) ∧ Sz l lam r (x - y)) ∧ (∀ (r s : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam s y → Sz l lam (r + s) (x * y)) ∧ (∀ (r s : ℝ) (x : ℂ), r ≤ s → Sz l lam r x → Sz l lam s x) ∧ (∀ n : ℤ, Sz l lam 0 (n : ℂ)) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (x : κ → ℂ), (∀ k ∈ t, Sz l lam r (x k)) → Sz l lam r (∑ k ∈ t, x k)) :=
  fun _ _ _ => ⟨sz_zero, fun _ _ _ hx hy => ⟨sz_add hx hy, sz_sub hx hy⟩, fun _ _ _ _ hx hy => sz_mul hx hy,
    fun _ _ _ h hx => sz_mono h hx, sz_int, fun _ t _ _ h => sz_sum t h⟩

end GlobalTheory.QFam.SzSum
