import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem not_both {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p l : ℕ} (h : Nat.Coprime p l)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (l : Ω) < 1 := by
  intro hl
  have hg : ((Nat.gcd p l : ℕ) : ℤ) = (p : ℤ) * Nat.gcdA p l + (l : ℤ) * Nat.gcdB p l := Nat.gcd_eq_gcd_ab p l
  rw [h.gcd_eq_one, Nat.cast_one] at hg
  have hΩ : (1 : Ω) = (p : Ω) * ((Nat.gcdA p l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB p l : ℤ) : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hg
    push_cast at this
    exact this
  have hint : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => A.valuation_le_one ⟨(z : Ω), intCast_mem A z⟩
  have h1 : A.valuation ((p : Ω) * ((Nat.gcdA p l : ℤ) : Ω)) < 1 := by
    rw [Valuation.map_mul]
    calc A.valuation (p : Ω) * A.valuation ((Nat.gcdA p l : ℤ) : Ω) ≤ A.valuation (p : Ω) * 1 := by
          gcongr
          exact hint _
      _ < 1 := by rw [mul_one]; exact hp
  have h2 : A.valuation ((l : Ω) * ((Nat.gcdB p l : ℤ) : Ω)) < 1 := by
    rw [Valuation.map_mul]
    calc A.valuation (l : Ω) * A.valuation ((Nat.gcdB p l : ℤ) : Ω) ≤ A.valuation (l : Ω) * 1 := by
          gcongr
          exact hint _
      _ < 1 := by rw [mul_one]; exact hl
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [← hΩ, Valuation.map_one] at h3
  exact lt_irrefl _ h3

theorem UpperTheory.V.Chr.locUnr :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e n : ℕ) (ψ : G ℚ Ω →* Oˣ), e ≠ 0 → n ≠ 0 → IsOpen (ψ.ker : Set (G ℚ Ω)) → ψ ^ n = 1 →
          ∀ (p : ℕ) (A : ValuationSubring Ω), p.Prime → p ≠ l → A.valuation (p : Ω) < 1 →
          ∀ (U' U : Subgroup (G ℚ Ω)) (h : U' ≤ U), U' = Ine (F := ℚ) A → U = Dec (F := ℚ) A →
          Module.length O (LinearMap.ker (resU (rho l e ψ) h)) ≤ (n.factorization l : ℕ∞) * eO l O ∧
            (U' ≤ ψ.ker → Function.Injective (resU (rho l e ψ) h)) := by
  intro Ω _ _ _ l _ O _ _ _ _ _ e n ψ he hn hopen hpow p A hp hpl hAp U' U h hU' hU
  subst hU' hU
  obtain ⟨hnorm, _, γ, hγ, hcl, hcyc⟩ := decCyc Ω p A hp hAp
  haveI := hnorm
  obtain ⟨_, hζ, heOtop, hchar⟩ := rootVal l O n hn
  haveI := hchar
  have hlprime : l.Prime := Fact.out
  have hlA : ¬ A.valuation (l : Ω) < 1 := not_both A ((Nat.coprime_primes hp hlprime).2 hpl) hAp
  have hIneCyc : Ine (F := ℚ) A ≤ (cycZ ℚ Ω l).ker := (places ℚ Ω l A).2.2.2 hlA
  have hcont : ContAction (rho l e ψ) := by
    have hk : IsOpen ((ψ⁻¹).ker : Set (G ℚ Ω)) := by
      have hkk : (ψ⁻¹).ker = ψ.ker := by
        ext g
        simp [MonoidHom.mem_ker]
      rw [hkk]
      exact hopen
    exact (contTw ℚ Ω l).2.2 O ψ⁻¹ (-(e : ℤ)) hk
  have hK := kerResCyc O (G ℚ Ω) (QO l O) (rho l e ψ) hcont (Ine (F := ℚ) A) (Dec (F := ℚ) A) h γ hγ hcl
  have hact : ∀ g m, rho l e ψ g m = (((ψ g)⁻¹ * (chiO ℚ Ω l O g) ^ (-(e : ℤ)) : Oˣ) : O) • m := by
    intro g m
    rw [rho, twist₂, scalRep_apply]
    rfl
  have hchiIne : ∀ g ∈ Ine (F := ℚ) A, chiO ℚ Ω l O g = 1 := by
    intro g hg
    have h1 : cycZ ℚ Ω l g = 1 := hIneCyc hg
    simp [chiO, h1]
  have hchiγ : ((chiO ℚ Ω l O γ : Oˣ) : O) = (p : O) := by
    have h1 := hcyc l hpl.symm
    show algebraMap ℤ_[l] O ((cycZ ℚ Ω l γ : ℤ_[l]ˣ) : ℤ_[l]) = (p : O)
    rw [h1]
    exact map_natCast (algebraMap ℤ_[l] O) p
  have hψn : ∀ g, (ψ g) ^ n = 1 := by
    intro g
    have := congrArg (fun f => f g) hpow
    simpa using this
  have hinj : Ine (F := ℚ) A ≤ ψ.ker → Function.Injective (resU (rho l e ψ) h) := by
    intro hker
    apply hK.2
    intro m _
    set c : Oˣ := (ψ γ)⁻¹ * (chiO ℚ Ω l O γ) ^ (-(e : ℤ)) with hcdef
    have hc1 : (c : O) - 1 ≠ 0 := by
      intro h0
      have hcU : c = 1 := Units.ext (sub_eq_zero.mp h0)
      have h2 : c ^ n = 1 := by rw [hcU, one_pow]
      have key : (chiO ℚ Ω l O γ) ^ (e * n) = (c ^ n)⁻¹ := by
        rw [hcdef, mul_pow, inv_pow, hψn γ, inv_one, one_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
          ← zpow_neg]
        congr 1
        push_cast
        ring
      rw [h2, inv_one] at key
      have hv := congrArg (fun u : Oˣ => (u : O)) key
      simp only [Units.val_pow_eq_pow_val, hchiγ, Units.val_one] at hv
      have hv' : ((p ^ (e * n) : ℕ) : O) = ((1 : ℕ) : O) := by push_cast; exact hv
      have hnat := Nat.cast_injective hv'
      exact absurd hnat (Nat.one_lt_pow (Nat.mul_ne_zero he hn) hp.one_lt).ne'
    obtain ⟨m', hm'⟩ := (qoFacts l O).2.2.1 ((c : O) - 1) hc1 m
    refine ⟨m', ?_, ?_⟩
    · rw [H0U, mem_riemannRochSpace_iff_regularAt_everywhere]
      intro g
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hact, hchiIne g g.2, hker g.2]
      simp
    · rw [hact, ← hm', sub_smul, one_smul]
  refine ⟨?_, hinj⟩
  by_cases hker : Ine (F := ℚ) A ≤ ψ.ker
  · have hbot : LinearMap.ker (resU (rho l e ψ) h) = ⊥ := LinearMap.ker_eq_bot.mpr (hinj hker)
    rw [hbot]
    simp
  · obtain ⟨g, hg, hgk⟩ := SetLike.not_le_iff_exists.mp hker
    set ζ : O := (((ψ g)⁻¹ : Oˣ) : O) with hζdef
    have hζn : ζ ^ n = 1 := by
      rw [hζdef, ← Units.val_pow_eq_pow_val, inv_pow, hψn g, inv_one, Units.val_one]
    have hζ1 : ζ ≠ 1 := by
      intro h1
      apply hgk
      rw [MonoidHom.mem_ker]
      have : ((ψ g)⁻¹ : Oˣ) = 1 := Units.ext h1
      exact inv_eq_one.mp this
    have hsub : H0U (rho l e ψ) (Ine (F := ℚ) A) ≤ ((ζ - 1) • LinearMap.id : QO l O →ₗ[O] QO l O).ker := by
      intro m hm
      rw [H0U, mem_riemannRochSpace_iff_regularAt_everywhere] at hm
      have h1 := hm ⟨g, hg⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hact, hchiIne g hg] at h1
      simp only [one_zpow, mul_one] at h1
      rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, sub_smul, one_smul, hζdef, h1, sub_self]
    have hbound : Module.length O (H0U (rho l e ψ) (Ine (F := ℚ) A)) ≤ (n.factorization l : ℕ∞) * eO l O := by
      refine (Module.length_le_of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)).trans ?_
      rw [(qoFacts l O).2.2.2]
      exact hζ ζ hζn hζ1
    have hfin : Module.length O (H0U (rho l e ψ) (Ine (F := ℚ) A)) ≠ ⊤ :=
      ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.coe_ne_top _) heOtop) hbound
    have hmono : H0U (rho l e ψ) (Dec (F := ℚ) A) ≤ H0U (rho l e ψ) (Ine (F := ℚ) A) := by
      intro m hm
      rw [H0U, mem_riemannRochSpace_iff_regularAt_everywhere] at hm ⊢
      intro g
      exact hm ⟨g, h g.2⟩
    exact (hK.1 hfin).trans ((Module.length_le_of_injective (Submodule.inclusion hmono)
      (Submodule.inclusion_injective hmono)).trans hbound)
