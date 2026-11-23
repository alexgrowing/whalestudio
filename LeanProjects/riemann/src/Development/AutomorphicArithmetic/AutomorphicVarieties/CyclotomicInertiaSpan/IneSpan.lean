import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.OnePrimeOfTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.Minkowski
import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.B1

theorem UpperTheory.V.B1.ineSpan :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N : Subgroup (G ℚ Ω)) (S : Finset ℕ) (B : ℕ → ValuationSubring Ω), IsOpen (N : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ N →
    (∀ p ∈ S, p.Prime ∧ (B p).valuation (p : Ω) < 1) →
    (∀ B' : ValuationSubring Ω, (∀ p ∈ S, ¬ B'.valuation (p : Ω) < 1) → Ine (F := ℚ) B' ≤ N) → N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) = ⊤ := by
  intro Ω _ _ _ N S B ho hc hB hI
  have hle : ∀ p ∈ S, Ine (F := ℚ) (B p) ≤ N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) := fun p hp =>
    (le_iSup₂ (f := fun p (_ : p ∈ S) => Ine (F := ℚ) (B p)) p hp).trans le_sup_right
  have hN : N ≤ N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) := le_sup_left
  generalize N ⊔ (⨆ p ∈ S, Ine (F := ℚ) (B p)) = M at hle hN
  have hn : M.Normal := Subgroup.Normal.of_commutator_le _ (hc.trans hN)
  refine B3.minkowski Ω M hn (Subgroup.isOpen_mono hN ho) fun B' => ?_
  by_cases h : ∀ p ∈ S, ¬ B'.valuation (p : Ω) < 1
  · exact (hI B' h).trans hN
  · push Not at h
    obtain ⟨p, hp, hv⟩ := h
    obtain ⟨g, hg⟩ := (B3.placesQ Ω).2.2 p (B p) B' (hB p hp).1 (hB p hp).2 hv
    intro x hx
    have := hn.conj_mem _ (hle p hp (hg x hx)) g
    simpa [mul_assoc] using this
