import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RamFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem place_uniq {l : ℕ} (hl : l.Prime) (v w : HeightOneSpectrum (𝓞 ℚ)) (hv : (l : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : (l : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have key : ∀ u : HeightOneSpectrum (𝓞 ℚ), (l : 𝓞 ℚ) ∈ u.asIdeal →
      Ideal.span {(l : ℤ)} = u.asIdeal.map (e : 𝓞 ℚ →+* ℤ) := by
    intro u hu
    apply hmax.eq_of_le
    · rw [Ideal.map_comap_of_equiv]
      exact Ideal.comap_ne_top _ u.isPrime.ne_top
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hel : e (l : 𝓞 ℚ) = (l : ℤ) := map_natCast e l
      rw [← hel]
      exact Ideal.mem_map_of_mem _ hu
  apply HeightOneSpectrum.ext
  rw [← Ideal.map_of_equiv (I := v.asIdeal) e, ← Ideal.map_of_equiv (I := w.asIdeal) e, ← key v hv, ← key w hw]

theorem UpperTheory.exists_finite_place_set_factoring_through_GS :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
          {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
          ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S) (η' : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* ℤˣ) (Ψ' : GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) →* c.Oˣ),
            ContainsAbove S l ∧ (∀ v, IsPlaceOver (A v) v.1) ∧ D.ι.range = Dec (F := ℚ) (A v₀) ∧ (∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀) ∧
            η'.comp (toGS Ω _) = D.η ∧ Ψ'.comp (toGS Ω _) = D.Ψ := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  classical
  have hlp : l.Prime := Fact.out
  obtain ⟨-, -, -, hηlc, -, -, -, -, -, -, -⟩ := dat_facts D
  haveI : IsScalarTower ℚ K Ω := inferInstance
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨⟨T, hT⟩, -⟩ := ramFinite ℚ ℚ K Ω
  have hlN0 : ((l * N : ℕ) : 𝓞 ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hlp.ne_zero (NeZero.ne N))
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((l * N : ℕ) : 𝓞 ℚ)}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := T ∪ hfin.toFinset
  have hmemS : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ S := by
    intro v hv
    apply Finset.mem_union_right
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv
  have hcast : ∀ n : ℕ, algebraMap ℚ Ω (((n : 𝓞 ℚ)) : ℚ) = (n : Ω) := fun n => by simp
  have hlv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v hv
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hv
  have hNv : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v hv
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ hv
  obtain ⟨A₀, hA₀l, hA₀dec, -⟩ := dat_loc D
  have hA₀top : A₀ ≠ ⊤ := by
    intro h
    exact ((places ℚ Ω l A₀).2.1 h).2 hA₀l
  obtain ⟨v₀, hv₀⟩ := (places ℚ Ω l A₀).1 hA₀top
  have hlv₀ : ((l : ℕ) : 𝓞 ℚ) ∈ v₀.asIdeal := by
    rw [← hv₀, hcast]
    exact hA₀l
  have hv₀S : v₀ ∈ S := hmemS v₀ (hlv v₀ hlv₀)
  let v₀' : S := ⟨v₀, hv₀S⟩
  let A : S → ValuationSubring Ω := fun v =>
    if v.1 = v₀ then A₀ else Classical.choose (exists_isPlaceOver Ω v.1)
  let H : Subgroup (G ℚ Ω) := (cycZ ℚ Ω l).ker ⊓ (Chr.cls ℚ Ω N).ker ⊓ D.η.ker
  have hHclosed : IsClosed (H : Set (G ℚ Ω)) := by
    simp only [H, Subgroup.coe_inf]
    refine (IsClosed.inter ?_ ?_).inter ?_
    · rw [MonoidHom.coe_ker]
      exact isClosed_singleton.preimage (contTw ℚ Ω l).1
    · exact Subgroup.isClosed_of_isOpen _ (Chr.clsFacts ℚ Ω N).1
    · exact Subgroup.isClosed_of_isOpen _ (hηlc.isOpen_fiber 1)
  have hNS : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ H := by
    apply Subgroup.topologicalClosure_minimal _ _ hHclosed
    apply Subgroup.normalClosure_le_normal
    simp only [Set.iUnion_subset_iff]
    intro v hv B hB g hg
    have hg' : g ∈ Ine (F := ℚ) B := hg
    have hvS : v ∉ S := hv
    have hvT : v ∉ T := fun h => hvS (Finset.mem_union_left _ h)
    have hlB : ¬ B.valuation (l : Ω) < 1 := by
      intro h
      rw [← hcast] at h
      exact hvS (hmemS v (hlv v ((hB _).mp h)))
    have hNB : ¬ B.valuation (N : Ω) < 1 := by
      intro h
      rw [← hcast] at h
      exact hvS (hmemS v (hNv v ((hB _).mp h)))
    refine ⟨⟨(places ℚ Ω l B).2.2.2 hlB hg', (Chr.clsFacts ℚ Ω N).2.2.2.2 B hNB hg'⟩, ?_⟩
    show g ∈ D.η.ker
    rw [D.η_ker]
    exact hT v hvT B hB ⟨by rw [galOf_self]; trivial, hg'⟩
  have hηk : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ D.η.ker := hNS.trans inf_le_right
  have hΨk : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ D.Ψ.ker := by
    intro g hg
    have hH := hNS hg
    have h1 : cycZ ℚ Ω l g = 1 := hH.1.1
    have h2 : Chr.cls ℚ Ω N g = 1 := hH.1.2
    rw [MonoidHom.mem_ker]
    simp [Dat.Ψ, Chr.Psi, chiO, Chr.dirG, h1, h2]
  refine ⟨S, A, v₀', QuotientGroup.lift _ D.η hηk, QuotientGroup.lift _ D.Ψ hΨk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact hmemS v (hlv v hv)
  · intro v
    by_cases h : v.1 = v₀
    · simp only [A, if_pos h]
      rw [h]
      exact hv₀
    · simp only [A, if_neg h]
      exact Classical.choose_spec (exists_isPlaceOver Ω v.1)
  · simp only [A, v₀', if_pos rfl]
    exact hA₀dec
  · intro v
    constructor
    · intro hv
      exact Subtype.ext (place_uniq hlp _ _ hv hlv₀)
    · rintro rfl
      exact hlv₀
  · ext g
    rfl
  · ext g
    rfl
