import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SplitPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ex_place (K : Type) [Field K] [NumberField K] {w : ℕ} (hw : w.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), (w : 𝓞 K) ∈ v.asIdeal := by
  have hwZ : Prime (w : ℤ) := Nat.prime_iff_prime_int.mp hw
  haveI hPm : (Ideal.span {(w : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hwZ.irreducible
  obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K)
    (Ideal.span {(w : ℤ)}) (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have hx0 : x = 0 := (algebraMap ℤ (𝓞 K)).injective_int (by rw [hx, map_zero])
      rw [hx0]
      exact Ideal.zero_mem _)
  have hmem : (w : 𝓞 K) ∈ Q := by
    have hc : (w : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      rw [hQ]
      exact Ideal.mem_span_singleton_self _
    simpa using hc
  refine ⟨⟨Q, hQm.isPrime, ?_⟩, hmem⟩
  intro hbot
  rw [hbot, Ideal.mem_bot] at hmem
  exact hw.ne_zero (by exact_mod_cast hmem)

private theorem prime_eq {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (h1 : (p : 𝓞 K) ∈ v.asIdeal) (h2 : (q : 𝓞 K) ∈ v.asIdeal) : p = q := by
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hb := Nat.gcd_eq_gcd_ab p q
  rw [hc.gcd_eq_one] at hb
  have hone : (1 : 𝓞 K) ∈ v.asIdeal := by
    have e : (1 : 𝓞 K) = (p : 𝓞 K) * ((Nat.gcdA p q : ℤ) : 𝓞 K) + (q : 𝓞 K) * ((Nat.gcdB p q : ℤ) : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) hb
      push_cast at this
      exact this
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ h2)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

theorem UpperTheory.V.Ws.Gys.placesQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → ∀ U : Subgroup (G T.F Ω), IsOpen (U : Set (G T.F Ω)) →
      Set.Infinite {v : HeightOneSpectrum (𝓞 T.F) | (∃ w : ℕ, w.Prime ∧ T.Splits w ∧ (w : 𝓞 T.F) ∈ v.asIdeal) ∧ ∀ A, IsPlaceOver A v → Dec (F := T.F) A ≤ U} := by
  intro Ω _ _ _ l _ c D T hD U hU
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hr, ho, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have hemb := (UpperTheory.V.Base.galEmbTop ℚ T.F Ω).1
  have hrng := (UpperTheory.V.Base.galEmbTop ℚ T.F Ω).2.1
  have hoe : Topology.IsOpenEmbedding (UpperTheory.V.Base.galEmb ℚ T.F Ω) := by
    refine ⟨hemb, ?_⟩
    rw [← MonoidHom.coe_range, UpperTheory.V.Base.range_galEmb]
    exact hrng
  have hmo : IsOpen ((U.map (resQ T.F) : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    rw [Subgroup.coe_map]
    exact hoe.isOpenMap _ hU
  let H : Subgroup (G ℚ Ω) := U.map (resQ T.F) ⊓ D.rbar.ker ⊓ D.om.ker
  have hHo : IsOpen (H : Set (G ℚ Ω)) := IsOpen.inter (IsOpen.inter hmo hr) ho
  have hinf := Gys.splitPrimes Ω H hHo
  obtain ⟨v0, -⟩ := ex_place T.F Nat.prime_two
  let f : ℕ → HeightOneSpectrum (𝓞 T.F) := fun w => if hw : w.Prime then (ex_place T.F hw).choose else v0
  have hf : ∀ w (hw : w.Prime), (w : 𝓞 T.F) ∈ (f w).asIdeal := by
    intro w hw
    simp only [f, dif_pos hw]
    exact (ex_place T.F hw).choose_spec
  have himg := hinf.image (f := f) (by
    intro a ha b hb hab
    exact prime_eq (f a) ha.1 hb.1 (hf a ha.1) (by rw [hab]; exact hf b hb.1))
  refine himg.mono ?_
  rintro _ ⟨w, ⟨hwp, hwD⟩, rfl⟩
  refine ⟨⟨w, hwp, ?_, hf w hwp⟩, ?_⟩
  · unfold Tower.Splits
    intro A hA g hg
    have hg' := hwD A hA hg
    obtain ⟨hg12, hg3⟩ := Subgroup.mem_inf.mp hg'
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg12
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, hg2⟩, hg3⟩
    obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hg1
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  · intro A hA σ hσ
    have hv : A.valuation (w : Ω) < 1 := by
      have h0 := (hA (w : 𝓞 T.F)).mpr (hf w hwp)
      simpa using h0
    have hdec : resQ T.F σ ∈ Dec (F := ℚ) A := by
      rw [mem_Dec] at hσ ⊢
      exact hσ
    have hH := hwD A hv hdec
    obtain ⟨τ, hτ, he⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hH).1).1
    have hτσ : τ = σ := hemb.injective he
    exact hτσ ▸ hτ
