import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationApplyOfWild

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.Rt.wild_mem_ker
    {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} (hl : l.Prime)
    {A : ValuationSubring Ω} (hvl : ¬ A.valuation (l : Ω) < 1) {N : Type} [Group N]
    (ψ : Ine (F := F) A →* N) (ho : IsOpen (ψ.ker : Set (Ine (F := F) A))) (hψ : ∀ σ, ψ σ ^ l = 1)
    (σ : Ine (F := F) A) (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ.1 y / y - 1) < 1) : ψ σ = 1 := by
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 ho
  have h1t : (1 : G F Ω) ∈ t := by
    have h1 : (1 : Ine (F := F) A) ∈ (Subtype.val ⁻¹' t : Set (Ine (F := F) A)) := by
      rw [hte]
      exact ψ.ker.one_mem
    exact h1
  obtain ⟨L, hfin, hL⟩ := (krullTopology_mem_nhds_one_iff F Ω t).1 (ht.mem_nhds h1t)
  have hfix : ∃ n, 0 < n ∧ ∀ x ∈ L, (σ.1 ^ n) x = x := by
    let f : ℕ → (L →ₐ[F] Ω) := fun i => ((σ.1 ^ i : G F Ω) : Ω →ₐ[F] Ω).comp L.val
    obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite f
    wlog hlt : i < j generalizing i j
    · exact this j i hij.symm he.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)
    refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    intro x hx
    have hx' := congrArg (fun φ => φ ⟨x, hx⟩) he
    simp only [f, AlgHom.comp_apply, IntermediateField.val_mk, AlgHom.coe_coe] at hx'
    have hx'' : (σ.1 ^ i) x = (σ.1 ^ j) x := hx'
    have hj : σ.1 ^ j = σ.1 ^ i * σ.1 ^ (j - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hj, AlgEquiv.mul_apply] at hx''
    exact ((σ.1 ^ i).injective hx'').symm
  obtain ⟨n, hn0, hn⟩ := hfix
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0.ne' l hl.ne_one
  have hτw := GlobalTheory.WildInertiaChar.wild_pow A σ.1 hσ m
  have hk : ¬ A.valuation ((l ^ a : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow]
    exact not_lt.2 (one_le_pow₀ (not_lt.1 hvl))
  have hτ : σ.1 ^ m ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    apply GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ.1 ^ m) hτw (l ^ a) hk x
    rw [← pow_mul, mul_comm, ← hnm]
    exact hn x hx
  have hker : σ ^ m ∈ ψ.ker := by
    have h2 : (σ ^ m) ∈ (Subtype.val ⁻¹' t : Set (Ine (F := F) A)) := hL hτ
    rw [hte] at h2
    exact h2
  rw [MonoidHom.mem_ker, map_pow] at hker
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
  have hg := pow_gcd_eq_one.2 ⟨hψ σ, hker⟩
  rwa [hcop.gcd_eq_one, pow_one] at hg

theorem UpperTheory.V.Ws.Rt.tameExp :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ¬ A.valuation (l : Ω) < 1 →
      ∀ (M : Type) [Monoid M] (φ : Ine (F := F) A →* M), IsLocallyConstant φ → (∀ σ, φ σ ^ l = 1) →
      ∀ θ : Ine (F := F) A →* Multiplicative (ZMod l), IsOpen (θ.ker : Set (Ine (F := F) A)) → θ ≠ 1 → ∀ σ, θ σ = 1 → φ σ = 1 := by
  intro F Ω _ _ _ _ _ l _ A hvl M _ φ hφ hφl θ hθo hθ1 σ hσ
  have hl : l.Prime := Fact.out
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := F) A
  let φ' := φ.toHomUnits
  have hφ'o : IsOpen (SetLike.coe φ'.ker) := by
    have hf := hφ.isOpen_fiber 1
    convert hf using 1
    ext x
    simp [φ', MonoidHom.mem_ker, Units.ext_iff]
  have hφ'l : ∀ τ, φ' τ ^ l = 1 := by
    intro τ
    apply Units.ext
    simp [φ', hφl]
  have hθl : ∀ τ, θ τ ^ l = 1 := by
    intro τ
    rw [← ofAdd_toAdd (θ τ), ← ofAdd_nsmul]
    simp
  have wφ : ∀ τ : Ine (F := F) A, (∀ y : Ω, y ≠ 0 → A.valuation (τ.1 y / y - 1) < 1) → φ' τ = 1 :=
    fun τ hτ => UpperTheory.V.Ws.Rt.wild_mem_ker hl hvl φ' hφ'o hφ'l τ hτ
  have wθ : ∀ τ : Ine (F := F) A, (∀ y : Ω, y ≠ 0 → A.valuation (τ.1 y / y - 1) < 1) → θ τ = 1 :=
    fun τ hτ => UpperTheory.V.Ws.Rt.wild_mem_ker hl hvl θ hθo hθl τ hτ
  have hθγ : θ ⟨γ, hγ.1⟩ ≠ 1 := by
    intro h
    apply hθ1
    ext τ
    have hm := GlobalTheory.TameCharUnique.mem_of_tameGen hγ θ.ker (θ.ker.isClosed_of_isOpen hθo) h
      (fun τ hτ => wθ τ hτ) τ
    simpa [MonoidHom.mem_ker] using hm
  let Φ := φ'.prod θ
  let S := (Subgroup.zpowers (Φ ⟨γ, hγ.1⟩)).comap Φ
  have hle : φ'.ker ⊓ θ.ker ≤ S := by
    intro τ hτ
    have h1 : Φ τ = 1 := by
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hτ
      simp [Φ, hτ.1, hτ.2]
    show Φ τ ∈ Subgroup.zpowers (Φ ⟨γ, hγ.1⟩)
    rw [h1]
    exact Subgroup.one_mem _
  have hSo : IsOpen (SetLike.coe S) := by
    apply Subgroup.isOpen_mono hle
    rw [Subgroup.coe_inf]
    exact hφ'o.inter hθo
  have hσS := GlobalTheory.TameCharUnique.mem_of_tameGen hγ S (S.isClosed_of_isOpen hSo)
    (Subgroup.mem_zpowers _)
    (fun τ hτ => by
      have h1 : Φ τ = 1 := by simp [Φ, wφ τ hτ, wθ τ hτ]
      show Φ τ ∈ Subgroup.zpowers (Φ ⟨γ, hγ.1⟩)
      rw [h1]
      exact Subgroup.one_mem _) σ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hσS
  have hk1 : φ' ⟨γ, hγ.1⟩ ^ k = φ' σ := by
    have := congrArg Prod.fst hk
    simpa [Φ] using this
  have hk2 : θ ⟨γ, hγ.1⟩ ^ k = θ σ := by
    have := congrArg Prod.snd hk
    simpa [Φ] using this
  rw [hσ] at hk2
  have hord : orderOf (θ ⟨γ, hγ.1⟩) = l := orderOf_eq_prime (hθl _) hθγ
  have hdvd : (l : ℤ) ∣ k := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.2 hk2
  obtain ⟨j, rfl⟩ := hdvd
  have hu : φ' σ = 1 := by
    rw [← hk1, zpow_mul, zpow_natCast, hφ'l, one_zpow]
  have hv := congrArg Units.val hu
  simpa [φ'] using hv
