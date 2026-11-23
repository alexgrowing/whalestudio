import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeSign

theorem sign_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ x ∈ s, f x ≠ 0) :
    0 < (-1 : ℝ) ^ (s.filter fun x => f x < 0).card * ∏ x ∈ s, f x := by
  have e : (-1 : ℝ) ^ (s.filter fun x => f x < 0).card
      = ∏ x ∈ s, (if f x < 0 then (-1 : ℝ) else 1) := by
    rw [Finset.prod_ite]; simp
  rw [e, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro x hx
  split_ifs with hneg
  · linarith
  · have : 0 < f x := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm (h x hx))
    linarith

theorem sign_div {a b P Q : ℝ} (hP : 0 < a * P) (hQ : 0 < b * Q) : 0 < a * b * (P / Q) := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp at hQ
  have e : a * b * (P / Q) = (a * P) * (b * Q) / Q ^ 2 := by
    field_simp
  rw [e]
  exact div_pos (mul_pos hP hQ) (by positivity)

theorem above_eq {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (r : ℝ) :
    above d d' r = (univ.filter fun k => r < d k).card + (univ.filter fun j => r < d' j).card := by
  unfold above
  simp only [Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  congr!

theorem pfSign {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hinj : Function.Injective (Sum.elim d d')) :
    (∀ i, 0 < (-1 : ℝ) ^ above d d' (d i) * pfD d d' i) ∧
      ∀ j, 0 < (-1 : ℝ) ^ above d d' (d' j) * pfR d d' j := by
  have hd : ∀ {i k}, k ≠ i → d i - d k ≠ 0 := by
    intro i k hk h
    apply hk
    have := hinj (a₁ := Sum.inl k) (a₂ := Sum.inl i) (by simpa using (sub_eq_zero.mp h).symm)
    simpa using this
  have hd' : ∀ {j k}, k ≠ j → d' j - d' k ≠ 0 := by
    intro j k hk h
    apply hk
    have := hinj (a₁ := Sum.inr k) (a₂ := Sum.inr j) (by simpa using (sub_eq_zero.mp h).symm)
    simpa using this
  have hx : ∀ i j, d i - d' j ≠ 0 := by
    intro i j h
    have := hinj (a₁ := Sum.inl i) (a₂ := Sum.inr j) (by simpa using sub_eq_zero.mp h)
    simp at this
  have hy : ∀ j i, d' j - d i ≠ 0 := by
    intro j i h
    exact hx i j (by linarith)
  constructor
  · intro i
    have h1 := sign_prod (univ.erase i) (fun k => d i - d k)
      (fun k hk => hd (Finset.ne_of_mem_erase hk))
    have h2 := sign_prod (univ : Finset (Fin m)) (fun j => d i - d' j) (fun j _ => hx i j)
    have e1 : ((univ.erase i).filter fun k => d i - d k < 0) = univ.filter fun k => d i < d k := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, sub_neg]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rintro rfl
        exact lt_irrefl _ h
    have e2 : (univ.filter fun j => d i - d' j < 0) = univ.filter fun j => d i < d' j := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg]
    rw [e1] at h1
    rw [e2] at h2
    rw [above_eq, pow_add]
    exact sign_div h1 h2
  · intro j
    have h1 := sign_prod (univ : Finset (Fin (m + 1))) (fun i => d' j - d i) (fun i _ => hy j i)
    have h2 := sign_prod (univ.erase j) (fun k => d' j - d' k)
      (fun k hk => hd' (Finset.ne_of_mem_erase hk))
    have e1 : (univ.filter fun i => d' j - d i < 0) = univ.filter fun i => d' j < d i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg]
    have e2 : ((univ.erase j).filter fun k => d' j - d' k < 0)
        = univ.filter fun k => d' j < d' k := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, sub_neg]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rintro rfl
        exact lt_irrefl _ h
    rw [e1] at h1
    rw [e2] at h2
    rw [above_eq, pow_add]
    exact sign_div h1 h2

end GlobalTheory.CompanionTheory.RgHeSign
