import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.cardUnion :
    ∀ (P : Type) (S : ℕ → Set P) (b : ℕ), Monotone S → (∀ x, ∃ n, x ∈ S n) → (∀ n, CardLe (S n) b) → CardLe P b := by
  intro P S b hmono hcov hcard
  choose m hm using hcov
  have key : ∀ T : Finset P, T.card ≤ b := by
    intro T
    classical
    obtain ⟨hfN, hbN⟩ := hcard (T.sup m)
    have hsub : (↑T : Set P) ⊆ S (T.sup m) := by
      intro x hx
      exact hmono (Finset.le_sup (f := m) hx) (hm x)
    have hfin : (S (T.sup m)).Finite := Set.toFinite _
    have h1 := Nat.card_mono hfin hsub
    have h2 : Nat.card (↑T : Set P) = T.card := by simp
    omega
  have hfin : Finite P := by
    by_contra hnot
    rw [not_finite_iff_infinite] at hnot
    obtain ⟨T, hT⟩ := Infinite.exists_subset_card_eq P (b + 1)
    have := key T
    omega
  refine ⟨hfin, ?_⟩
  have := Fintype.ofFinite P
  classical
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact key _
