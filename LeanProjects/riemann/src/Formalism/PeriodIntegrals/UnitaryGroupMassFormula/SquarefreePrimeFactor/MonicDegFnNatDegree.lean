import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.BigPrimes

open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor.W

variable {g : ℕ} [Fact g.Prime]

theorem monicDeg_fn_monic (d : ℕ) (c : Fin d → ZMod g) :
    (X ^ d + ∑ i, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

theorem monicDeg_fn_natDegree (d : ℕ) (c : Fin d → ZMod g) :
    (X ^ d + ∑ i, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).natDegree = d := by
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt c

theorem monicDeg_fn_coeff (d : ℕ) (c : Fin d → ZMod g) (i : Fin d) :
    (X ^ d + ∑ j, C (c j) * X ^ (j : ℕ) : (ZMod g)[X]).coeff i = c i := by
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.is_lt), zero_add, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (Fin.ext h).symm
  · simp

theorem mem_monicDeg {d : ℕ} {f : (ZMod g)[X]} :
    f ∈ monicDeg g d ↔ f.Monic ∧ f.natDegree = d := by
  constructor
  · intro hf
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hf
    exact ⟨monicDeg_fn_monic d c, monicDeg_fn_natDegree d c⟩
  · rintro ⟨hm, hd⟩
    refine Finset.mem_image.2 ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    show X ^ d + ∑ i : Fin d, C (f.coeff i) * X ^ (i : ℕ) = f
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) d]
    have h := hm.as_sum
    rw [hd] at h
    exact h.symm

theorem card_monicDeg (d : ℕ) : (monicDeg g d).card = g ^ d := by
  unfold monicDeg
  rw [Finset.card_image_of_injective]
  · simp [Finset.card_univ, ZMod.card]
  · intro c c' h
    funext i
    have := congrArg (fun f : (ZMod g)[X] => f.coeff i) h
    simpa only [monicDeg_fn_coeff] using this

open Classical in
theorem mem_irrDeg {d : ℕ} {q : (ZMod g)[X]} :
    q ∈ irrDeg g d ↔ (q.Monic ∧ q.natDegree = d) ∧ Irreducible q := by
  unfold irrDeg
  rw [Finset.mem_filter, mem_monicDeg]

end PI.SqfPrimeFactor.W
