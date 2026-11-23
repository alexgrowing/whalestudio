import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PartOrd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.cases :
    ∀ (h : Host) (t : ℕ), h.Big t → ∀ (O : Type) [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N), h.IsChar ψ → ∀ l e : ℕ, l.Prime → l ≠ 2 → 0 < e → e < t →
      (l ∉ Bchi h.chi → ¬ l ∣ orderOf ψ ∧ comp l ψ ^ 2 = 1 ∧ th0 l ψ = ψ ∧ kap l ψ = 1 ∧ (l - 1 ∣ 2 * e → chiP l ψ = ψ) ∧
        (h.CaseI l e ∨ h.CaseZ l e ψ ∨ h.CaseII l e ψ ∨ h.CaseIII l e ψ)) ∧
      (l ∈ Bchi h.chi → h.CaseII l e ψ ∨ h.CaseIV l e ψ ∨ h.CaseV l e) := by
  intro h t hbig O _ _ ψ hψ l e hl hl2 he het
  have hB := bchiFacts h t hbig
  have hC := hostComp h O ψ hψ
  refine ⟨fun hnB => ?_, fun hinB => ?_⟩
  · obtain ⟨_, hlo, hlq, _, _, _, _, hE⟩ := hB.2.2.2.2 l hl hl2 hnB
    have hCl := hC.2.2 l hl hl2
    have hord : ¬ l ∣ orderOf ψ := by
      intro hd
      have hd' := hd.trans hC.1
      rcases (Nat.Prime.dvd_mul hl).1 hd' with h2 | h2
      · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h2))
      · exact hlo h2
    have hP := (partOrd _ l hl ψ hC.2.1).2.2.2.2.2.1 hord
    have hth : th0 l ψ = ψ := hP.2
    have hchi : l - 1 ∣ 2 * e → chiP l ψ = ψ := by
      intro hdiv
      have hc1 : comp l ψ = 1 := hCl.2.2.2 (hE e he het hdiv).2.2
      show th0 l ψ * (comp l (th0 l ψ))⁻¹ = ψ
      rw [hth, hc1, inv_one, mul_one]
    refine ⟨hord, hCl.2.2.1 hlq, hth, hP.1, hchi, ?_⟩
    by_cases hdiv : l - 1 ∣ 2 * e
    · by_cases h1 : ψ = 1
      · exact Or.inr (Or.inl ⟨hnB, hdiv, h1⟩)
      · by_cases hodd : Odd (orderOf ψ)
        · exact Or.inr (Or.inr (Or.inr ⟨hnB, hdiv, hodd, h1⟩))
        · refine Or.inr (Or.inr (Or.inl ⟨(hE e he het hdiv).1, ?_, Or.inr hdiv⟩))
          show Even (orderOf (chiP l ψ))
          rw [hchi hdiv]
          exact Nat.not_odd_iff_even.mp hodd
    · exact Or.inl ⟨hnB, hdiv⟩
  · by_cases he1 : e = 1
    · exact Or.inr (Or.inr ⟨hinB, he1⟩)
    · have h2e : 2 ≤ e := by omega
      by_cases hev : Even (orderOf (chiP l ψ))
      · exact Or.inl ⟨h2e, hev, Or.inl hinB⟩
      · exact Or.inr (Or.inl ⟨hinB, h2e, Nat.not_even_iff_odd.mp hev⟩)
