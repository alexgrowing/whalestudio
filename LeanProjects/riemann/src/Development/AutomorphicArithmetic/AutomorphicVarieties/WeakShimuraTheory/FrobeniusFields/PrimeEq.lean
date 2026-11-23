import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem prime_eq {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h1 : A.valuation (p : Ω) < 1) (h2 : A.valuation (q : Ω) < 1) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have hi : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n => (A.valuation_le_one_iff _).2 (intCast_mem A n)
  have h3 : A.valuation ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hi a)) h1
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hi b)) h2
  have h4 : (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h4, map_one] at h3
  exact lt_irrefl _ h3

theorem UpperTheory.V.Ws.away :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → (∀ (A : ValuationSubring Ω) (p q : ℕ), p.Prime → q.Prime → A.valuation (p : Ω) < 1 → A.valuation (q : Ω) < 1 → p = q) ∧ (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, D.om g = 1 ∧ D.Psi g = D.ψ g) ∧ (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ D.ξ.ker) ∧ (∀ σ : G ℚ Ω, IsCC σ → D.om σ = -1) ∧ ∀ (A : ValuationSubring Ω) (p : ℕ), p.Prime → p ∉ D.S → A.valuation (p : Ω) < 1 → Raw.Away D.S A ∧ ∀ g ∈ Ine (F := ℚ) A, D.Psi g = 1 ∧ D.ξ g = 1 ∧ D.om g = 1 := by
  intro Ω _ _ _ l hl c D hD
  have hom : IsOmT c D.om := ⟨hD.om_pow, fun σ => by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hD.om_bar σ⟩
  obtain ⟨-, -, -, -, hcc, hunr, -, -⟩ := (omT Ω l c).2 D.om hom
  have h2 : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A,
      D.om g = 1 ∧ D.Psi g = D.ψ g := fun A hA g hg => by
    refine ⟨hunr A hA hg, ?_⟩
    have h1 : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hA hg
    have h3 : chiO ℚ Ω l c.O g = 1 := by rw [chiO, MonoidHom.comp_apply, h1, map_one]
    show chiO ℚ Ω l c.O g ^ (D.e : ℤ) * D.ψ g = D.ψ g
    rw [h3, one_zpow, one_mul]
  refine ⟨prime_eq, h2, fun A hA g hg => ?_, fun σ hσ => hcc σ hσ hD.l_odd, fun A p hp hS hA => ?_⟩
  · obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l A (D.pl l) hl.out hA (hD.pl_over l hl.out)
    have h1 := hD.xi_unrT l (Finset.mem_insert_self _ _) (hu g hg)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, inv_mul_cancel_comm] at h1
    exact h1
  · have ha : Raw.Away D.S A := fun q hq h => hS (prime_eq A p q hp (hD.S_prime q hq) hA h ▸ hq)
    refine ⟨ha, fun g hg => ?_⟩
    obtain ⟨e1, e2⟩ := h2 A (ha l hD.l_mem) g hg
    exact ⟨e2.trans (hD.psi_unr A ha hg), hD.xi_unr A ha hg, e1⟩
