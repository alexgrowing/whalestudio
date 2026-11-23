import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.UpperBlockRankOneUpdate
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

noncomputable section

open Matrix PositivityTheory.SiegelWeilFormula.Act.C4.Bq

namespace PositivityTheory.SiegelWeilFormula.Act.C6.M

variable {R : Type} [CommRing R] (s : R →+* R) (e : R) {n : ℕ} (i₀ : Fin n)

def U (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) : Prop := Mᵀ * kunf.jw n e * M.map s = kunf.jw n e

variable {s e i₀}

theorem qms_inl (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (a : Fin n) (d : Fin n ⊕ Fin n) :
    (kunf.jw n e * M.map s) (Sum.inl a) d = s (M (Sum.inr a) d) := by
  simp [kunf.jw, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem qms_inr (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (a : Fin n) (d : Fin n ⊕ Fin n) :
    (kunf.jw n e * M.map s) (Sum.inr a) d = e * s (M (Sum.inl a) d) := by
  simp [kunf.jw, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.smul_apply]

theorem U_apply {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hU : U s e M) (c d : Fin n ⊕ Fin n) :
    ∑ r, M r c * (kunf.jw n e * M.map s) r d = kunf.jw n e c d := by
  have := congrFun (congrFun hU c) d
  rw [Matrix.mul_assoc, Matrix.mul_apply] at this
  simpa [Matrix.transpose_apply] using this

theorem shift_coordinates_column {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M)
    (W : Fin n ⊕ Fin n → R) : ∑ r, M r (Sum.inl i₀) * W r = W (Sum.inl i₀) := by
  have h : ∀ r, M r (Sum.inl i₀) = if r = Sum.inl i₀ then 1 else 0 := fun r => by
    rw [NQ.apply hN (Or.inl rfl), Matrix.one_apply]
  simp_rw [h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem col_c {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M)
    {c : Fin n ⊕ Fin n} (hcx : c ≠ Sum.inl i₀) (hcy : c ≠ Sum.inr i₀) (W : Fin n ⊕ Fin n → R) :
    ∑ r, M r c * W r = W c + M (Sum.inl i₀) c * W (Sum.inl i₀) := by
  have h : ∀ r, M r c = (if r = c then 1 else 0) + (if r = Sum.inl i₀ then M (Sum.inl i₀) c else 0) := by
    intro r
    by_cases hr : r = Sum.inl i₀
    · subst hr; rw [if_neg (Ne.symm hcx), if_pos rfl, zero_add]
    · rw [NQ.apply hN (Or.inr ⟨hcy, hr⟩), Matrix.one_apply]; simp [hr]
  rw [Finset.sum_congr rfl fun r _ => congrArg (· * W r) (h r)]
  simp_rw [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_split' {A : Type} [AddCommMonoid A] {m : ℕ} (em : Fin m → Fin n) (hem : Function.Injective em)
    (hrng : ∀ k, k ≠ i₀ ↔ k ∈ Set.range em) (f : Fin n → A) : ∑ a, f a = f i₀ + ∑ j, f (em j) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  congr 1
  rw [← Finset.sum_image (fun a _ b _ h => hem h)]
  congr 1
  ext k
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, true_and]
  exact hrng k

theorem columnBlock (hs : ∀ a, s (s a) = a) (he : e * e = 1) (hse : s e = e) {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hU : U s e M) (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    M (Sum.inr i₀) (Sum.inr i₀) = 1 ∧ (∀ k, k ≠ i₀ → s (M (Sum.inr k) (Sum.inr i₀)) = -M (Sum.inl i₀) (Sum.inl k)) ∧
      ∀ k, k ≠ i₀ → s (M (Sum.inl k) (Sum.inr i₀)) = -(e * M (Sum.inl i₀) (Sum.inr k)) := by
  set W : Fin n ⊕ Fin n → R := fun r => (kunf.jw n e * M.map s) r (Sum.inr i₀) with hW
  have hyy : s (M (Sum.inr i₀) (Sum.inr i₀)) = 1 := by
    have h1 := U_apply hU (Sum.inl i₀) (Sum.inr i₀)
    rw [shift_coordinates_column hN W] at h1
    simp only [hW, qms_inl] at h1
    simpa [kunf.jw] using h1
  refine ⟨by rw [← hs (M _ _), hyy, map_one], fun k hk => ?_, fun k hk => ?_⟩
  · have h1 := U_apply hU (Sum.inl k) (Sum.inr i₀)
    rw [col_c hN (by simpa using hk) (by simp) W] at h1
    have h2 : s (M (Sum.inr k) (Sum.inr i₀)) + M (Sum.inl i₀) (Sum.inl k) = 0 := by
      simp only [hW, qms_inl, hyy, mul_one] at h1
      simpa [kunf.jw, Matrix.one_apply_ne hk] using h1
    exact eq_neg_of_add_eq_zero_left h2
  · have h1 := U_apply hU (Sum.inr k) (Sum.inr i₀)
    rw [col_c hN (by simp) (by simpa using hk) W] at h1
    have h2 : e * s (M (Sum.inl k) (Sum.inr i₀)) + M (Sum.inl i₀) (Sum.inr k) = 0 := by
      simp only [hW, qms_inl, qms_inr, hyy, mul_one] at h1
      simpa [kunf.jw] using h1
    have h3 := eq_neg_of_add_eq_zero_left h2
    calc s (M (Sum.inl k) (Sum.inr i₀)) = e * (e * s (M (Sum.inl k) (Sum.inr i₀))) := by rw [← mul_assoc, he, one_mul]
      _ = -(e * M (Sum.inl i₀) (Sum.inr k)) := by rw [h3, mul_neg]

theorem nq_unique (hs : ∀ a, s (s a) = a) (he : e * e = 1) (hse : s e = e)
    {M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : U s e M) (hN : U s e N)
    (hMq : NQ (Sum.inl i₀) (Sum.inr i₀) M) (hNq : NQ (Sum.inl i₀) (Sum.inr i₀) N)
    (hrow : ∀ c, M (Sum.inl i₀) c = N (Sum.inl i₀) c) : M = N := by
  obtain ⟨hM1, hM2, hM3⟩ := columnBlock hs he hse hM hMq
  obtain ⟨hN1, hN2, hN3⟩ := columnBlock hs he hse hN hNq
  have hinj : Function.Injective s := fun a b h => by rw [← hs a, h, hs b]
  ext r c
  by_cases hrx : r = Sum.inl i₀
  · subst hrx; exact hrow c
  by_cases hcy : c = Sum.inr i₀
  · subst hcy
    rcases r with k | k
    · have hk : k ≠ i₀ := fun h => hrx (by rw [h])
      exact hinj (by rw [hM3 k hk, hN3 k hk, hrow])
    · by_cases hk : k = i₀
      · subst hk; rw [hM1, hN1]
      · exact hinj (by rw [hM2 k hk, hN2 k hk, hrow])
  · rw [NQ.apply hMq (Or.inr ⟨hcy, hrx⟩), NQ.apply hNq (Or.inr ⟨hcy, hrx⟩)]

theorem even_im_hermitian_sub (hs : ∀ a, s (s a) = a) (he : e * e = 1) (hse : s e = e) {m : ℕ} (em : Fin m → Fin n)
    (hem : Function.Injective em) (hrng : ∀ k, k ≠ i₀ ↔ k ∈ Set.range em) {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hU : U s e M) (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    s (M (Sum.inl i₀) (Sum.inr i₀) + ∑ j, M (Sum.inl i₀) (Sum.inr (em j)) * s (M (Sum.inl i₀) (Sum.inl (em j)))) =
      -(e * (M (Sum.inl i₀) (Sum.inr i₀) + ∑ j, M (Sum.inl i₀) (Sum.inr (em j)) * s (M (Sum.inl i₀) (Sum.inl (em j))))) := by
  obtain ⟨h1, h2, h3⟩ := columnBlock hs he hse hU hN
  have hem0 : ∀ j, em j ≠ i₀ := fun j => (hrng (em j)).2 ⟨j, rfl⟩
  have hl : ∀ j, M (Sum.inl (em j)) (Sum.inr i₀) = -(e * s (M (Sum.inl i₀) (Sum.inr (em j)))) := fun j => by
    rw [← hs (M (Sum.inl (em j)) (Sum.inr i₀)), h3 _ (hem0 j), map_neg, map_mul, hse]
  have hr : ∀ j, M (Sum.inr (em j)) (Sum.inr i₀) = -s (M (Sum.inl i₀) (Sum.inl (em j))) := fun j => by
    rw [← hs (M (Sum.inr (em j)) (Sum.inr i₀)), h2 _ (hem0 j), map_neg]
  have hyy : M (Sum.inr i₀) (Sum.inr i₀) = 1 := h1
  have h0 := U_apply hU (Sum.inr i₀) (Sum.inr i₀)
  rw [Fintype.sum_sum_type] at h0
  simp only [qms_inl, qms_inr] at h0
  rw [sum_split' em hem hrng (fun a => M (Sum.inl a) (Sum.inr i₀) * s (M (Sum.inr a) (Sum.inr i₀))),
    sum_split' em hem hrng (fun a => M (Sum.inr a) (Sum.inr i₀) * (e * s (M (Sum.inl a) (Sum.inr i₀))))] at h0
  simp only [hl, hr, hyy, map_one, map_neg, map_mul, hs, hse, kunf.jw, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] at h0
  set α := M (Sum.inl i₀) (Sum.inr i₀)
  set S1 := ∑ j, s (M (Sum.inl i₀) (Sum.inr (em j))) * M (Sum.inl i₀) (Sum.inl (em j))
  set S2 := ∑ j, M (Sum.inl i₀) (Sum.inr (em j)) * s (M (Sum.inl i₀) (Sum.inl (em j)))
  have hA : ∑ j, -(e * s (M (Sum.inl i₀) (Sum.inr (em j)))) * -M (Sum.inl i₀) (Sum.inl (em j)) = e * S1 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hB : ∑ j, -s (M (Sum.inl i₀) (Sum.inl (em j))) * (e * -(e * M (Sum.inl i₀) (Sum.inr (em j)))) = (e * e) * S2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hA, hB, he, one_mul] at h0
  have hS : s S2 = S1 := by
    simp only [S2, S1, map_sum, map_mul, hs]
  rw [map_add, hS]
  linear_combination e * h0 - (s α + S1) * he

end PositivityTheory.SiegelWeilFormula.Act.C6.M

end
