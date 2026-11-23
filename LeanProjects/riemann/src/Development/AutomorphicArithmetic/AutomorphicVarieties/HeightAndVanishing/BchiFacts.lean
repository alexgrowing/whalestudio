import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.primesex

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.bchiFacts :
    ∀ (h : Host) (t : ℕ), h.Big t → (∀ l ∈ Bchi h.chi, l < h.q1 ∧ l < h.d) ∧ pK h.chi ∈ Bchi h.chi ∧ ¬ pK h.chi ∣ h.N ∧ ¬ pOne h.chi ∣ h.N ∧
      ∀ l, l.Prime → l ≠ 2 → l ∉ Bchi h.chi → 5 ≤ l ∧ ¬ l ∣ h.o ∧ ¬ l ∣ h.q ∧ l ≠ pK h.chi ∧ ¬ l ∣ hStar h.chi ∧ l ≠ pOne h.chi ∧
        ¬ l ∣ h.H.index ∧ ∀ e, 0 < e → e < t → l - 1 ∣ 2 * e → 2 ≤ e ∧ l ≤ 2 * t ∧ ¬ l ∣ h.N := by
  intro h t hB
  obtain ⟨ht1, ht2, hy⟩ := hB
  obtain ⟨hidx, -, -, ho, -, hNp, -⟩ := hostIndex h
  obtain ⟨⟨hKp, -, hK7, hKc⟩, ⟨hOp, -, hOc⟩, -⟩ := pK_pOne_prime_conditions h.chi
  have eq : h.q = h.chi.N := rfl
  have eo : h.o = ordC h.chi := rfl
  obtain ⟨yq1, yqd⟩ := hy h.q (by simp)
  obtain ⟨yo1, yod⟩ := hy h.o (by simp)
  obtain ⟨yK1, yKd⟩ := hy (pK h.chi) (by simp)
  obtain ⟨yS1, ySd⟩ := hy (hStar h.chi) (by simp)
  obtain ⟨yO1, yOd⟩ := hy (pOne h.chi) (by simp)
  have hS0 : hStar h.chi ≠ 0 := (NumberField.classNumber_pos (K := Kstar (pK h.chi))).ne'
  have hq0 : h.chi.N ≠ 0 := h.chi.ne.out
  have hP0 : ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨⟨ho.ne', hq0⟩, hKp.ne_zero⟩, hS0⟩, hOp.ne_zero⟩
  have memB : ∀ l, l.Prime → l ≠ 2 → l ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi →
      l ∈ Bchi h.chi := by
    intro l hl hl2 hlP
    simp only [Bchi, Finset.mem_insert, Finset.mem_erase, Nat.mem_primeFactors]
    exact Or.inr ⟨hl2, hl, hlP, hP0⟩
  have dO : ordC h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    (((dvd_mul_right _ _).mul_right _).mul_right _).mul_right _
  have dq : h.chi.N ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    (((dvd_mul_left _ _).mul_right _).mul_right _).mul_right _
  have dK : pK h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    ((dvd_mul_left _ _).mul_right _).mul_right _
  have dS : hStar h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    (dvd_mul_left _ _).mul_right _
  have dO1 : pOne h.chi ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi :=
    dvd_mul_left _ _
  refine ⟨?_, memB _ hKp (by omega) dK, ?_, ?_, ?_⟩
  · intro l hl
    simp only [Bchi, Finset.mem_insert, Finset.mem_erase, Nat.mem_primeFactors] at hl
    rcases hl with rfl | ⟨-, hlp, hlP, -⟩
    · exact ⟨by omega, by omega⟩
    · have le : ∀ y, y ≠ 0 → l ∣ y → l ≤ y := fun y hy0 hly => Nat.le_of_dvd (Nat.pos_of_ne_zero hy0) hly
      rcases hlp.dvd_mul.mp hlP with h4 | h5
      · rcases hlp.dvd_mul.mp h4 with h3 | hS
        · rcases hlp.dvd_mul.mp h3 with h2 | hK
          · rcases hlp.dvd_mul.mp h2 with hO | hQ
            · have := le _ ho.ne' hO
              exact ⟨by omega, by omega⟩
            · have := le _ hq0 hQ
              exact ⟨by omega, by omega⟩
          · have := le _ hKp.ne_zero hK
            exact ⟨by omega, by omega⟩
        · have := le _ hS0 hS
          exact ⟨by omega, by omega⟩
      · have := le _ hOp.ne_zero h5
        exact ⟨by omega, by omega⟩
  · intro hd'
    rcases (hNp _ hKp).mp hd' with h2 | hq' | h1 | h1
    · omega
    · exact (Nat.Prime.coprime_iff_not_dvd hKp).mp hKc hq'
    · omega
    · omega
  · intro hd'
    have nd := (Nat.Prime.coprime_iff_not_dvd hOp).mp hOc
    rcases (hNp _ hOp).mp hd' with h2 | hq' | h1 | h1
    · exact nd (by rw [h2]; exact dvd_mul_of_dvd_left (dvd_mul_right 2 _) _)
    · exact nd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hq' 2) _)
    · omega
    · omega
  · intro l hl hl2 hlB
    have h3 : l ≠ 3 := by
      intro e
      subst e
      exact hlB (Finset.mem_insert_self _ _)
    have h5 : 5 ≤ l := by
      by_contra hc
      have := hl.two_le
      interval_cases l
      · exact hl2 rfl
      · exact h3 rfl
      · norm_num at hl
    have nd : ∀ y, y ∣ ordC h.chi * h.chi.N * pK h.chi * hStar h.chi * pOne h.chi → ¬ l ∣ y :=
      fun y hy hly => hlB (memB l hl hl2 (hly.trans hy))
    refine ⟨h5, nd _ dO, nd _ dq, fun e => nd _ dK (by rw [e]), nd _ dS, fun e => nd _ dO1 (by rw [e]), ?_, ?_⟩
    · intro hi
      rcases hl.dvd_mul.mp (hi.trans hidx) with h2 | hO
      · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h2))
      · exact nd _ dO hO
    · intro e he0 het hle
      have hl1 : l - 1 ≤ 2 * e := Nat.le_of_dvd (by omega) hle
      refine ⟨by omega, by omega, fun hN => ?_⟩
      rcases (hNp l hl).mp hN with h2 | hq' | h1 | h1
      · exact hl2 h2
      · exact nd _ dq hq'
      · omega
      · omega
