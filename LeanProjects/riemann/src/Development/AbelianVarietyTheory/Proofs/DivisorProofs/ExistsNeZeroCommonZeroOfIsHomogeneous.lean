import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeHeightSpanRangeXMvPolynomial
open IsLocalRing

namespace GlobalTheory

theorem exists_ne_zero_common_zero_of_isHomogeneous :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (f : Fin r → MvPolynomial (Fin n) k),
      (∀ i, ∃ d, 0 < d ∧ (f i).IsHomogeneous d) → r < n →
        ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro k _ _ n r f hf hrn
  by_contra hcon
  push Not at hcon
  set I : Ideal (MvPolynomial (Fin n) k) := Ideal.span (Set.range f) with hIdef
  set M : Ideal (MvPolynomial (Fin n) k) :=
    MvPolynomial.vanishingIdeal k ({(0 : Fin n → k)} : Set (Fin n → k)) with hMdef
  have hMmax : M.IsMaximal := inferInstance

  have hf0 : ∀ i, MvPolynomial.eval (0 : Fin n → k) (f i) = 0 := by
    intro i
    obtain ⟨d, hd, hh⟩ := hf i
    rw [MvPolynomial.eval_zero]
    rw [MvPolynomial.constantCoeff_eq]
    apply hh.coeff_eq_zero
    simp
    omega
  have hIM : I ≤ M := by
    rw [hIdef, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, hMdef, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact hf0 i

  have hZ : MvPolynomial.zeroLocus k I ⊆ ({(0 : Fin n → k)} : Set (Fin n → k)) := by
    intro x hx
    by_contra hx0
    obtain ⟨i, hi⟩ := hcon x hx0
    apply hi
    have := hx (f i) (Ideal.subset_span ⟨i, rfl⟩)
    exact this
  have hMrad : M ≤ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I]
    exact MvPolynomial.vanishingIdeal_anti_mono hZ
  have hXM : Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))
      ≤ M := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, hMdef, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  have hItop : I ≠ ⊤ := fun h => hMmax.ne_top (top_le_iff.mp (h ▸ hIM))
  have hrad : I.radical.height = I.height := by
    rw [Ideal.height_eq_inf_minimalPrimes, Ideal.height_eq_inf_minimalPrimes,
      Ideal.radical_minimalPrimes]
  have hfin : (I.spanFinrank : ℕ∞) ≤ r := by
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := MvPolynomial (Fin n) k)
      (Set.finite_range f)
    have h2 : (Set.range f).ncard ≤ r := by
      rw [← Set.image_univ]
      refine (Set.ncard_image_le Set.finite_univ).trans ?_
      simp [Set.ncard_univ]
    exact_mod_cast h1.trans h2
  have key : (n : ℕ∞) ≤ r :=
    (GlobalTheory.le_height_span_range_X_mvPolynomial k n).trans <| (Ideal.height_mono hXM).trans <| (Ideal.height_mono hMrad).trans <|
      hrad.le.trans <| (Ideal.height_le_spanFinrank I hItop).trans hfin
  have : n ≤ r := by exact_mod_cast key
  omega

end GlobalTheory
