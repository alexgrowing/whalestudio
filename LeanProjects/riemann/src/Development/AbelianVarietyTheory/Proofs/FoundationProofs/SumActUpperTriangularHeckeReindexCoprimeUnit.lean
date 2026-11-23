import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem Tower.sum_act_upper_mul_unit {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (c : X.Fn l) (hc : ∀ t : ℤ, X.act l !![1, t; 0, 1] c = c) (q : ℕ) (e : ℤ) (hq : 0 < q)
    (he : IsCoprime e (q : ℤ)) :
    ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c =
      ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  set f : ℤ → X.Fn l := fun r => X.act l !![1, r; 0, (q : ℤ)] c with hf
  have step : ∀ x : ℤ, X.act l !![1, x; 0, (q : ℤ)] c = f (x % q) := by
    intro x
    have hm : !![1, x; 0, (q : ℤ)] = !![(1 : ℤ), x / q; 0, 1] * !![1, x % q; 0, (q : ℤ)] := by
      have := Int.emod_add_mul_ediv x q
      ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
    rw [hm, ← Tower.act_act Ω ε X l _ _ (by simp [Matrix.det_fin_two]) (by simp [Matrix.det_fin_two]; exact hq), hc]
  let g : ℕ → ℕ := fun j => (((j : ℤ) * e) % q).toNat
  have hg : ∀ j, ((g j : ℕ) : ℤ) = ((j : ℤ) * e) % q := fun j =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hq'.ne')
  have hgr : ∀ j, g j < q := fun j => by
    have h1 := Int.emod_lt_of_pos ((j : ℤ) * e) hq'
    have h2 := hg j
    omega
  have hinj : Set.InjOn g (Finset.range q) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have h : ((i : ℤ) * e) % q = ((j : ℤ) * e) % q := by rw [← hg, ← hg, hij]
    have hd : (q : ℤ) ∣ ((j : ℤ) - i) * e := by
      rw [sub_mul]; exact (Int.ModEq.dvd h)
    have hd' : (q : ℤ) ∣ (j : ℤ) - i := he.symm.dvd_of_dvd_mul_right hd
    have h0 := Int.eq_zero_of_abs_lt_dvd hd' (by rw [abs_lt]; constructor <;> omega)
    omega
  have himg : (Finset.range q).image g = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr; simp only [Finset.mem_image] at hr; obtain ⟨j, _, rfl⟩ := hr; exact Finset.mem_range.2 (hgr j)
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c
      = ∑ j ∈ Finset.range q, f ((g j : ℕ) : ℤ) := by
        refine Finset.sum_congr rfl fun j _ => ?_; rw [step, hg]
    _ = ∑ r ∈ (Finset.range q).image g, f (r : ℤ) := (Finset.sum_image (f := fun r : ℕ => f (r : ℤ)) hinj).symm
    _ = ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by rw [himg]

end GlobalTheory.KZ
