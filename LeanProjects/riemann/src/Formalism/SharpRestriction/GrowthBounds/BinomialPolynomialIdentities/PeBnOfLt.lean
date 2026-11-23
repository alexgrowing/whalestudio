import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RestPathFrom

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem iv_inj (N n : ℕ) : Function.Injective (iv N n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [iv, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) h.2

theorem pe_Bn_of_lt {N : ℕ} (B : Fin N → ℕ) {i : ℕ} (h : i < N) : Bn B i = B ⟨i, h⟩ := by simp [Bn, h]

theorem Bn_of_ge {N : ℕ} (B : Fin N → ℕ) {i : ℕ} (h : ¬ i < N) : Bn B i = 0 := by simp [Bn, h]

theorem expSet_eq (n N : ℕ) (B : Fin N → ℕ) :
    (fun m : Fin N × Fin n →₀ ℕ => m.mapDomain (iv N n)) '' {m | ∀ i, multideg m i = B i} =
      {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then Bn B i else 0} := by
  ext e
  constructor
  · rintro ⟨m, hm, rfl⟩ i
    by_cases h : i < N
    · rw [if_pos h, pe_Bn_of_lt B h, ← hm ⟨i, h⟩]
      unfold multideg
      refine Finset.sum_congr rfl fun a _ => ?_
      have : ((i, a) : ℕ × Fin n) = iv N n (⟨i, h⟩, a) := rfl
      rw [this, Finsupp.mapDomain_apply (iv_inj N n)]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun a _ => ?_
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨⟨x, y⟩, hxy⟩
      simp only [iv, Prod.mk.injEq] at hxy
      exact h (hxy.1 ▸ x.2)
  · intro he
    have hsupp : (↑e.support : Set (ℕ × Fin n)) ⊆ Set.range (iv N n) := by
      rintro ⟨i, a⟩ hia
      by_cases h : i < N
      · exact ⟨(⟨i, h⟩, a), rfl⟩
      · exfalso
        have h0 := he i
        rw [if_neg h] at h0
        have := (Finset.sum_eq_zero_iff.mp h0) a (Finset.mem_univ a)
        simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hia
        exact hia this
    refine ⟨e.comapDomain (iv N n) (iv_inj N n).injOn, ?_, Finsupp.mapDomain_comapDomain _ (iv_inj N n) e hsupp⟩
    intro i
    have h0 := he i.val
    rw [if_pos i.2, pe_Bn_of_lt B i.2] at h0
    rw [← h0]
    unfold multideg
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.comapDomain_apply]
    rfl

theorem restPol : RestPol := by
  intro R _ n N B
  rw [(Formalism.InvariantFactorPaths.GelfandTsetlinBases.polynomial_b_rank n N (Bn B)).2.2 R, ← expSet_eq, Pol, MvPolynomial.restrictSupport_eq_span,
    Submodule.map_span, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro m _
  simp [rename_monomial]

end Formalism.MainNotions.G.ColumnFamilies
