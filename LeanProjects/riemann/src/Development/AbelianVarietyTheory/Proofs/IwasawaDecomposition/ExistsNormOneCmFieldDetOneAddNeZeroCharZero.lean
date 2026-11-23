import Mathlib
open NumberField

namespace GlobalTheory.CMScalar
open Matrix Polynomial

theorem eval_charpolyRev_neg {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (w : K) :
    (-A).charpolyRev.eval w = (1 + w • A).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm w, sub_eq_add_neg]

theorem exists_unit_norm_one_det_ne_zero (L : Type) [Field L] [NumberField L] [IsCMField L] (K : Type) [Field K]
    [CharZero K] (n : ℕ) (M : (L →+* K) → Matrix (Fin n) (Fin n) K) :
    ∃ u : L, u * (IsCMField.complexConj L : L →+* L) u = 1 ∧ ∀ σ : L →+* K, (1 + σ u • M σ).det ≠ 0 := by
  classical
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := fun x => IsCMField.complexConj_apply_apply L x
  obtain ⟨y, hy⟩ : ∃ y : L, c y ≠ y := by
    by_contra h
    push_neg at h
    apply IsCMField.complexConj_ne_one L
    ext x
    exact h x
  set i : L := y - c y with hi
  have hi0 : i ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hci : c i = -i := by rw [hi, map_sub, hcc]; ring
  have hden : ∀ t : ℚ, (1 : L) + (t : L) * i ≠ 0 := by
    intro t h
    have h1 : (t : L) * i = -1 := by linear_combination h
    have h2 := congrArg c h1
    rw [map_mul, map_ratCast, hci, map_neg, map_one] at h2
    have : (2 : L) = 0 := by linear_combination h1 + h2
    exact two_ne_zero this
  let f : ℚ → L := fun t => (1 - (t : L) * i) / (1 + (t : L) * i)
  have hfu : ∀ t, f t * c (f t) = 1 := by
    intro t
    have hd := hden t
    have hd' : (1 : L) - (t : L) * i ≠ 0 := by
      intro h; apply hden (-t); push_cast; linear_combination h
    have e : c (f t) = (1 + (t : L) * i) / (1 - (t : L) * i) := by
      simp only [f, map_div₀, map_sub, map_add, map_one, map_mul, map_ratCast, hci]
      congr 1 <;> ring
    rw [e, div_mul_div_comm]
    exact (div_eq_one_iff_eq (mul_ne_zero hd hd')).2 (by ring)
  have hfinj : Function.Injective f := by
    intro s t hst
    simp only [f] at hst
    rw [div_eq_div_iff (hden s) (hden t)] at hst
    have h2 : (2 : L) * ((t : L) - s) * i = 0 := by linear_combination hst
    have : ((t : L) - s) = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h two_ne_zero
        · exact h
      · exact absurd h hi0
    have : ((t - s : ℚ) : L) = 0 := by push_cast; exact this
    exact (sub_eq_zero.1 (Rat.cast_eq_zero.1 this)).symm
  have hp : ∀ σ : L →+* K, (-(M σ)).charpolyRev ≠ 0 := by
    intro σ h
    have := Matrix.eval_charpolyRev (M := -(M σ))
    rw [h, Polynomial.eval_zero] at this
    exact zero_ne_one this
  let B : Set L := ⋃ σ : L →+* K, σ ⁻¹' ((-(M σ)).charpolyRev.roots.toFinset : Set K)
  have hB : B.Finite := by
    apply Set.finite_iUnion
    intro σ
    exact (Finset.finite_toSet _).preimage σ.injective.injOn
  have hS : (f ⁻¹' B).Finite := hB.preimage hfinj.injOn
  obtain ⟨t, ht⟩ := (Set.infinite_univ (α := ℚ)).diff hS |>.nonempty
  refine ⟨f t, hfu t, fun σ hσ => ht.2 ?_⟩
  simp only [Set.mem_preimage, B, Set.mem_iUnion]
  refine ⟨σ, ?_⟩
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots (hp σ), Polynomial.IsRoot, eval_charpolyRev_neg]
  exact hσ

end GlobalTheory.CMScalar
