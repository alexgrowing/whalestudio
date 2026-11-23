import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsDecompositionElementAtLXiPowFourNeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.BarFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.RedOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

open private dirG_pow dirG_one dirG_frob psi_exp from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsDecompositionElementAtLXiPowFourNeOne

theorem UpperTheory.V.Keep.bigOm :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ (κ : G ℚ Ω →* c.Oˣ) (j : ℕ), κ ^ l ^ j = 1 → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := ℚ) A, D.om g = 1 ∧ Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1 := by
  intro Ω _ _ _ l _ c D hC κ j hj A hA
  obtain ⟨hD, h, t, e, ψ, hB, he0, het, hX, hII, hO⟩ := hC
  obtain ⟨_, ξ', ξ₀, hprim, _, hξ₀, hξ⟩ := hO.xi
  have hlp : l.Prime := Fact.out
  have hl2 : l ≠ 2 := hD.l_odd
  have hl3 : 3 ≤ l := by
    have := hlp.two_le
    omega
  have hfrob : IsFrob (D.pl l) l (D.sg l) :=
    hD.sg_frob l (by unfold Raw.T; exact Finset.mem_insert_self _ _)
  have hσD : D.sg l ∈ Dec (F := ℚ) (D.pl l) := hfrob.1
  have hcop : l.Coprime (l - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hlp]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have homσ : D.om (D.sg l) = 1 := by
    apply large₂.redOne c (l - 1) hcop
    · have e1 : (D.om (D.sg l)) ^ (l - 1) = (D.om ^ (l - 1)) (D.sg l) := by
        rw [MonoidHom.pow_apply]
      rw [e1, hD.om_pow, MonoidHom.one_apply]
    · have h1 := hD.om_bar (D.sg l)
      simp only [Raw.bar] at h1
      rw [h1]
      simp [chiO, hD.sg_cyc]
  obtain ⟨hIsChar, _⟩ := (Host.mem_X h).mp hX
  obtain ⟨a, u, hu, hψu, hbound⟩ := psi_exp h ψ hIsChar hlp hl2
  set M := l ^ j * (2 ^ a * u) with hM
  set g := D.sg l ^ M with hg
  have hgD : g ∈ Dec (F := ℚ) (D.pl l) := Subgroup.pow_mem _ hσD M
  have hom : D.om g = 1 := by
    rw [hg, map_pow, homσ, one_pow]
  have hκ : κ g = 1 := by
    rw [hg, map_pow, hM, pow_mul, ← MonoidHom.pow_apply, hj, MonoidHom.one_apply, one_pow]
  have hψ : D.ψ g = 1 := by
    rw [hg, hO.psi, map_pow, hM, mul_comm, pow_mul, ← dirG_pow, hψu, dirG_one, one_pow]
  have hξ₀1 : ξ₀ = 1 := orderOf_eq_one_iff.mp hξ₀
  have hndvd : ¬ l ∣ 2 ^ h.nII l ψ := by
    intro hd
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).mp (hlp.dvd_of_dvd_pow hd))
  have hfr := dirG_frob ξ' hlp (hD.pl_over l hlp) hndvd hfrob
  have hξ4 : D.ξ g ^ 4 ≠ 1 := by
    intro h4
    have hval : ξ' (l : ZMod (2 ^ h.nII l ψ)) ^ (2 ^ (a + 2) * (l ^ j * u)) = 1 := by
      have e2 : D.ξ (D.sg l) = Chr.dirG ℚ Ω ξ' (D.sg l) := by
        rw [hξ, hξ₀1, MonoidHom.mul_apply, dirG_one, one_mul]
      have e3 : D.ξ g ^ 4 = D.ξ (D.sg l) ^ (2 ^ (a + 2) * (l ^ j * u)) := by
        rw [hg, map_pow, ← pow_mul, hM]
        congr 1
        ring
      rw [e3, e2] at h4
      have h5 := congrArg (fun x : (c.O)ˣ => (x : c.O)) h4
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at h5
      rw [hfr] at h5
      exact h5
    have hlt := UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one c.O (h.nII l ψ) ξ' hprim l (a + 2) (l ^ j * u)
      (hlp.odd_of_ne_two hl2) (by omega) ((hlp.odd_of_ne_two hl2).pow.mul hu) hval
    omega
  have hbarξ : Raw.bar D.ξ g ^ 4 ≠ 1 := by
    intro h4
    apply hξ4
    obtain ⟨m, hm, hξm⟩ := hD.xi_ord
    apply large₂.redOne c m hm
    · rw [← pow_mul, mul_comm, pow_mul, ← MonoidHom.pow_apply, hξm, MonoidHom.one_apply, one_pow]
    · simp only [Raw.bar] at h4
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact h4
  obtain ⟨w, hw1, _⟩ := (Chr.placesQ Ω).2.2 l (D.pl l) A hlp (hD.pl_over l hlp) hA
  have conj : ∀ χ : G ℚ Ω →* (c.O)ˣ, χ (w⁻¹ * g * w) = χ g := by
    intro χ
    rw [map_mul, map_mul, map_inv, mul_comm _ (χ g), inv_mul_cancel_right]
  refine ⟨w⁻¹ * g * w, hw1 g hgD, ?_, ?_, ?_, ?_⟩
  · rw [conj, hom]
  · rw [(barFacts D hD).2.2.2.2.1]
    simp only [Raw.bar, conj, hom, hψ, Units.val_one, map_one, one_pow, mul_one]
  · rw [conj, hκ]
  · simp only [Raw.bar, conj]
    exact hbarξ

theorem UpperTheory.V.Keep.loc2 {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (hC : Ctx2 D) (X : Set2 D) (T : Tower D) (hOn : X.On T) :
    ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → (∃ g ∈ Ine (F := T.F) A, Raw.bar D.om (resQ T.F g) ≠ 1) ∨
      ∃ g ∈ Dec (F := T.F) A, Raw.bar D.om (resQ T.F g) = 1 ∧ T.rb wPs g = 1 ∧ T.rb wAl g ≠ 1 := by
  intro A hA
  right
  have hD : D.Good := hC.1
  haveI := T.nF
  obtain ⟨j, hj⟩ := X.kap.pow
  obtain ⟨g, hgA, hom, hPs, hκ, hξ⟩ := UpperTheory.V.Keep.bigOm D hC X.κ j hj A hA
  have hsq : ∀ u : ℤˣ, u ^ 2 = 1 := fun u => by
    rcases Int.units_eq_one_or u with h | h <;> simp [h]
  have hH : g ^ 2 ∈ T.F.fixingSubgroup := by
    rw [hOn.1, Set2.mem_H]
    refine ⟨?_, ?_, ?_⟩
    · rw [map_pow, hsq]
      simp only [Raw.bar, map_pow, Units.val_pow_eq_pow_val, map_pow]
      have : (residue c.O) (↑(D.Psi g) : c.O) = 1 := hPs
      rw [this]
      simp
    · rw [map_pow, map_pow, hsq, hsq]
    · rw [map_pow, hκ, one_pow]
  obtain ⟨s, hs⟩ := exists_resQ hH
  have hfacts := (barFacts D hD).2.2.2.2.2.2.1 T
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · rw [resQ_Dec, hs]
    exact Subgroup.pow_mem _ hgA 2
  · rw [hs]
    simp [Raw.bar, hom]
  · rw [hfacts, hs]
    simp only [wPs, pow_zero, one_mul]
    have e : Raw.bar D.Psi (g ^ 2) = 1 := by
      simp only [Raw.bar, map_pow, Units.val_pow_eq_pow_val]
      have : (residue c.O) (↑(D.Psi g) : c.O) = 1 := hPs
      rw [this, one_pow]
    rw [e]
    split_ifs <;> simp
  · rw [hfacts, hs]
    simp only [wAl, Int.reduceNeg, neg_zero, zpow_zero, mul_one, zpow_one, ite_self]
    intro h
    apply hξ
    have e : Raw.bar D.ξ (g ^ 2) = Raw.bar D.ξ g ^ 2 := by
      simp only [Raw.bar, map_pow, Units.val_pow_eq_pow_val]
    rw [e] at h
    calc Raw.bar D.ξ g ^ 4 = (Raw.bar D.ξ g ^ 2) ^ 2 := by ring
      _ = 1 := by rw [h, one_pow]

theorem UpperTheory.V.Keep.loc3 {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (hD : D.Good) (h5 : 5 ≤ l) (T : Tower D)
    (hsq : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, g ^ 2 ∈ T.F.fixingSubgroup) :
    ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → (∃ g ∈ Ine (F := T.F) A, Raw.bar D.om (resQ T.F g) ≠ 1) ∨
      ∃ g ∈ Dec (F := T.F) A, Raw.bar D.om (resQ T.F g) = 1 ∧ T.rb wPs g = 1 ∧ T.rb wAl g ≠ 1 := by
  intro A hA
  left
  haveI := T.nF
  have hw : IsOmT c D.om := ⟨hD.om_pow, fun σ => Ideal.Quotient.eq.mp (hD.om_bar σ)⟩
  have key := ((omT Ω l c).2 D.om hw).2.2.2.2.2.2.1 A hA 2
  by_contra hne
  push_neg at hne
  have hcop : l.Coprime (l - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hl.out]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hle : Ine (F := ℚ) A ≤ (D.om ^ 2).ker := by
    intro g hg
    obtain ⟨s, hs⟩ := exists_resQ (F := T.F) (hsq A hA g hg)
    have hsI : s ∈ Ine (F := T.F) A := by
      rw [resQ_Ine, hs]
      exact Subgroup.pow_mem _ hg 2
    have h1 := hne s hsI
    rw [hs] at h1
    have h2 : D.om (g ^ 2) = 1 := by
      apply large₂.redOne c (l - 1) hcop
      · have e : (D.om (g ^ 2)) ^ (l - 1) = (D.om ^ (l - 1)) (g ^ 2) := by
          rw [MonoidHom.pow_apply]
        rw [e, hD.om_pow, MonoidHom.one_apply]
      · exact h1
    rw [MonoidHom.mem_ker, MonoidHom.pow_apply, ← map_pow]
    exact h2
  have := Nat.le_of_dvd (by norm_num) (key hle)
  omega
