import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.Adj2
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.BarFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem false_of_two_primes_valuation_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h1 : A.valuation (p : Ω) < 1) (h2 : A.valuation (q : Ω) < 1) : False := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hz : ((Nat.gcd p q : ℕ) : ℤ) = p * Nat.gcdA p q + q * Nat.gcdB p q := Nat.gcd_eq_gcd_ab p q
  rw [hc.gcd_eq_one] at hz
  have hΩ : (1 : Ω) = (p : Ω) * ((Nat.gcdA p q : ℤ) : Ω) + (q : Ω) * ((Nat.gcdB p q : ℤ) : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hz
    push_cast at this
    exact this
  have ha : A.valuation ((Nat.gcdA p q : ℤ) : Ω) ≤ 1 := A.valuation_le_one_iff _ |>.2 (intCast_mem A _)
  have hb : A.valuation ((Nat.gcdB p q : ℤ) : Ω) ≤ 1 := A.valuation_le_one_iff _ |>.2 (intCast_mem A _)
  have e1 : A.valuation ((p : Ω) * ((Nat.gcdA p q : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ha) h1
  have e2 : A.valuation ((q : Ω) * ((Nat.gcdB p q : ℤ) : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hb) h2
  have e3 := Valuation.map_add_lt _ e1 e2
  rw [← hΩ, map_one] at e3
  exact lt_irrefl _ e3

theorem UpperTheory.V.Ws.characterSubgroup_open_even_index_tame_power :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ X : Set2 D, IsOpen (X.H : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ X.H ∧ (∀ σ : G ℚ Ω, IsCC σ → σ ∈ X.H) ∧ Even X.H.index ∧ ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, ∃ m : ℕ, l.Coprime m ∧ g ^ m ∈ X.H := by
  intro Ω _ _ _ l _ c D hD X
  obtain ⟨_, _, _, _, _, _, _, ⟨m, hm, hpow⟩, hopen⟩ := barFacts D hD
  have hbarpow : ∀ (a : G ℚ Ω) (n : ℕ), Raw.bar D.Psi (a ^ n) = Raw.bar D.Psi a ^ n := by
    intro a n
    simp [Raw.bar]
  have hsub : ∀ g : G ℚ Ω, X.φ g = 1 → X.η g = 1 → X.η' g = 1 → X.κ g = 1 →
      Raw.bar D.Psi g = 1 → g ∈ X.H := by
    intro g h1 h2 h3 h4 h5
    rw [Set2.mem_H]
    refine ⟨?_, by rw [h2, h3], h4⟩
    rw [h5, h1]
    simp
  have hl : l.Prime := Fact.out
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hU : IsOpen ((X.φ.ker : Set (G ℚ Ω)) ∩ X.η.ker ∩ X.η'.ker ∩ X.κ.ker ∩
        {g | Raw.bar D.Psi g = 1}) :=
      (((X.hφ.opn.inter X.hη.opn).inter X.hη'.opn).inter X.kap.opn).inter hopen
    have h1 : (1 : G ℚ Ω) ∈ (X.φ.ker : Set (G ℚ Ω)) ∩ X.η.ker ∩ X.η'.ker ∩ X.κ.ker ∩
        {g | Raw.bar D.Psi g = 1} := by
      simp [Raw.bar]
    have hmem : (X.H : Set (G ℚ Ω)) ∈ nhds (1 : G ℚ Ω) := by
      refine Filter.mem_of_superset (hU.mem_nhds h1) ?_
      rintro g ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
      exact hsub g h1 h2 h3 h4 h5
    exact Subgroup.isOpen_of_mem_nhds _ hmem
  · rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    refine hsub _ ?_ ?_ ?_ ?_ ?_ <;>
      simp [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm, Raw.bar]
    all_goals
      rw [commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)]
      simp
  · intro σ hσ
    have hsq : σ ^ 2 = 1 := by
      obtain ⟨j, hj⟩ := hσ
      ext x
      apply j.injective
      rw [pow_two, AlgEquiv.mul_apply, hj, hj, Complex.conj_conj]
      rfl
    have hκ : X.κ σ = 1 := by
      obtain ⟨k, hk⟩ := X.kap.pow
      have e1 : X.κ σ ^ (l ^ k) = 1 := by
        have := congrArg (fun f => f σ) hk
        simpa using this
      have e2 : X.κ σ ^ 2 = 1 := by
        rw [← map_pow, hsq, map_one]
      have hcop : Nat.Coprime 2 (l ^ k) :=
        Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hD.l_odd))
      have := pow_gcd_eq_one.2 ⟨e2, e1⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    have hψ := X.psi_cc σ hσ
    rw [Set2.mem_H]
    refine ⟨?_, by rw [X.hη.cc σ hσ, X.hη'.cc σ hσ], hκ⟩
    simp [Raw.bar, hψ, X.hφ.cc σ hσ]
  · let f : G ℚ Ω →* ℤˣ := X.η * X.η'⁻¹
    have hle : X.H ≤ f.ker := by
      intro g hg
      rw [Set2.mem_H] at hg
      simp [f, hg.2.1]
    have hsurj : Function.Surjective f := by
      intro s
      obtain ⟨g', -, h2, h3, -⟩ := adj2 D hD X 1 1 s 1
      exact ⟨g', by simp [f, h2, h3]⟩
    have hidx : f.ker.index = 2 := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
      simp
    rw [even_iff_two_dvd, ← hidx]
    exact Subgroup.index_dvd_of_le hle
  · intro A hA g hg
    have hne : ∀ q : ℕ, q.Prime → q ∉ D.S → ¬ A.valuation (q : Ω) < 1 := by
      intro q hq hqS hv
      exact false_of_two_primes_valuation_lt_one A hq hl (fun e => hqS (e ▸ hD.l_mem)) hv hA
    have hφg : X.φ g = 1 := (MonoidHom.mem_ker).1 (X.hφ.unr A (hne _ X.hφ.prime X.hφ.nm) hg)
    have hηg : X.η g = 1 := (MonoidHom.mem_ker).1
      (X.hη.unr A (hne _ X.hη.prime (fun h => X.hη.nm (Finset.mem_insert_of_mem h))) hg)
    have hη'g : X.η' g = 1 := (MonoidHom.mem_ker).1
      (X.hη'.unr A (hne _ X.hη'.prime
        (fun h => X.hη'.nm (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))) hg)
    have hκg : X.κ g = 1 := (MonoidHom.mem_ker).1 (X.kap.unrL A hA hg)
    refine ⟨m, hm, hsub _ ?_ ?_ ?_ ?_ ?_⟩
    · rw [map_pow, hφg, one_pow]
    · rw [map_pow, hηg, one_pow]
    · rw [map_pow, hη'g, one_pow]
    · rw [map_pow, hκg, one_pow]
    · rw [hbarpow, hpow g]
