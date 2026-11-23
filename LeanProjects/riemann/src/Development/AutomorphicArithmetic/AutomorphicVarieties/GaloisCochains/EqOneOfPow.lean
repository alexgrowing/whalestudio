import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

open scoped Pointwise in
private theorem galEmb_mem_inertia (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω]
    [Algebra k Ω] [Algebra E Ω] [Algebra k E] [IsScalarTower k E Ω] (Av : ValuationSubring Ω)
    (σ : G E Ω) (hσ : σ ∈ Ine Av) : UpperTheory.V.Base.galEmb k E Ω σ ∈ Ine Av := by
  rw [mem_Ine] at hσ ⊢
  obtain ⟨hd, hv⟩ := hσ
  refine ⟨?_, fun x hx => by rw [UpperTheory.V.Base.galEmb_apply]; exact hv x hx⟩
  rw [MulAction.mem_stabilizer_iff] at hd ⊢
  conv_rhs => rw [← hd]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def,
    AlgEquiv.smul_def, UpperTheory.V.Base.galEmb_apply]

private theorem valuation_lt_one_iff_zero_or_inv_not_mem {Ω : Type} [Field Ω] (Av : ValuationSubring Ω) (x : Ω) :
    Av.valuation x < 1 ↔ (x = 0 ∨ x⁻¹ ∉ Av) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [← ValuationSubring.valuation_le_one_iff, not_le, map_inv₀]
    simp only [hx, false_or]
    rw [← map_inv₀, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]

open scoped Pointwise in
private theorem conj_mem_inertia_of_mem_inertia_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (Av : ValuationSubring Ω) (σ τ : G F Ω) (hτ : τ ∈ Ine (σ • Av)) : σ⁻¹ * τ * σ ∈ Ine Av := by
  rw [mem_Ine] at hτ ⊢
  obtain ⟨hd, hv⟩ := hτ
  rw [MulAction.mem_stabilizer_iff] at hd
  refine ⟨?_, fun x hx => ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hd, inv_smul_smul]
  · have hx' : σ x ∈ σ • Av := ValuationSubring.smul_mem_pointwise_smul σ x Av
      ((ValuationSubring.valuation_le_one_iff _ _).1 hx)
    have h := hv (σ x) ((ValuationSubring.valuation_le_one_iff _ _).2 hx')
    rw [valuation_lt_one_iff_zero_or_inv_not_mem] at h ⊢
    have he : (σ⁻¹ * τ * σ) x - x = σ⁻¹ (τ (σ x) - σ x) := by
      simp [map_sub]
    rw [he]
    rcases h with h | h
    · left; rw [h, map_zero]
    · right
      rw [← map_inv₀]
      intro hm
      apply h
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
      exact hm

private theorem eq_one_of_pow_coprime_in_pGroup {B : Type} [CommGroup B] {l : ℕ} (hl : l.Prime) (hB : IsPGroup l B)
    (y : B) (n : ℕ) (hn : ¬ l ∣ n) (hy : y ^ n = 1) : y = 1 := by
  obtain ⟨m, hm⟩ := hB y
  have h1 := orderOf_dvd_of_pow_eq_one hm
  have h2 := orderOf_dvd_of_pow_eq_one hy
  have hc : Nat.Coprime (l ^ m) n := Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hl).2 hn)
  have : orderOf y ∣ 1 := by
    rw [← hc]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

open UpperTheory.V.Base UpperTheory.V.Kum in
theorem UpperTheory.V.GC.cl :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] (Φ : Fr.Frame l k) (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (π : G F Ω →* Φ.Γ) (ι : ∀ v, Φ.Gv v →* G F Ω) (A : Φ.V → ValuationSubring Ω) (pl : Φ.V → HeightOneSpectrum (𝓞 F)) (e : Φ.Inf ≃ InfinitePlace F) (c : Φ.Inf → G F Ω), FLink l Φ S K π ι A pl e c → ∃ h : ℕ, h ≠ 0 ∧ ∀ (B : Type) [CommGroup B] [Finite B], IsPGroup l B → ∀ χ : Φ.G0 →* B,
    IsOpen (χ.ker : Set Φ.G0) → (∀ p : Φ.V × Bool, ∀ g ∈ Φ.Iv p.1, χ (Φ.loc2 p g) = 1) → ∀ g, χ g ^ h = 1 := by
  intro F Ω _ _ _ _ _ l _ k _ _ Φ S K π ι A pl e c hL
  classical
  set U : Subgroup (G F Ω) := Φ.del.ker.comap π with hU
  have hUo : IsOpen (U : Set (G F Ω)) := hL.g.cont.isOpen_preimage _ hL.del_open
  let Uc : ClosedSubgroup (G F Ω) := ⟨U, U.isClosed_of_isOpen hUo⟩
  set E : IntermediateField F Ω := IntermediateField.fixedField (Uc : Subgroup (G F Ω)) with hE
  have hEU : E.fixingSubgroup = U := InfiniteGalois.fixingSubgroup_fixedField Uc
  haveI : FiniteDimensional F E := (InfiniteGalois.isOpen_iff_finite E).1 (by rw [hEU]; exact hUo)
  haveI : NumberField E := inferInstance
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  have hgal : UpperTheory.V.Base.galOf F E Ω = U := by
    rw [← hEU]
    ext σ
    simp [UpperTheory.V.Base.galOf, IntermediateField.mem_fixingSubgroup_iff]
  refine ⟨2 * Nat.card (ClassGroup (𝓞 E)), ?_, ?_⟩
  · have : 0 < Nat.card (ClassGroup (𝓞 E)) := Nat.card_pos
    omega
  intro B _ _ hB χ hχo hχI g
  have hmemU : ∀ σ : G E Ω, π (UpperTheory.V.Base.galEmb F E Ω σ) ∈ Φ.del.ker := fun σ => by
    have := UpperTheory.V.Base.galEmb_mem F E Ω σ
    rw [hgal] at this
    exact this
  let f : G E Ω →* Φ.G0 := (π.comp (UpperTheory.V.Base.galEmb F E Ω)).codRestrict Φ.del.ker hmemU
  let ψ : G E Ω →* B := (χ.comp f) ^ 2
  have key : ∀ (Av : ValuationSubring Ω) (τ : G F Ω), τ ∈ Ine Av → ∀ hτ : π τ ∈ Φ.del.ker, χ ⟨π τ, hτ⟩ = 1 := by
    intro Av τ hτA hτ
    have hZ : ∀ y : Ω, IsIntegral ℤ y → y ∈ Av := by
      intro y hy
      have hy' : IsIntegral Av y := hy.tower_top
      obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hy'
      rw [← ha]
      exact a.2
    let φ : 𝓞 F →+* Av := ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict Av
      (fun x => hZ _ ((x.2).map (IsScalarTower.toAlgHom ℤ F Ω)))
    let P : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal Av).comap φ
    have hP : ∀ x : 𝓞 F, x ∈ P ↔ Av.valuation (algebraMap F Ω x) < 1 := by
      intro x
      exact (Av.valuation_lt_one_iff (φ x))
    by_cases hPb : P = ⊥
    · have hall : ∀ y : Ω, y ∈ Av := by
        intro y
        haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
        haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
        haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
        have halg : IsAlgebraic ℤ y := by
          rw [IsFractionRing.isAlgebraic_iff ℤ ℚ Ω]
          exact Algebra.IsAlgebraic.isAlgebraic y
        obtain ⟨m, hm0, hm⟩ := halg.exists_integral_multiple
        have h1 : m • y ∈ Av := hZ _ hm
        have hcast : algebraMap F Ω ((m : 𝓞 F) : F) = (m : Ω) := by simp
        have h2 : Av.valuation (m : Ω) = 1 := by
          have hnot : (m : 𝓞 F) ∉ P := by
            rw [hPb, Ideal.mem_bot]
            exact_mod_cast hm0
          rw [hP, hcast] at hnot
          have hle : Av.valuation (m : Ω) ≤ 1 := (Av.valuation_le_one_iff _).2 (intCast_mem Av m)
          exact le_antisymm hle (not_lt.1 hnot)
        rw [← Av.valuation_le_one_iff] at h1 ⊢
        rw [zsmul_eq_mul, map_mul, h2, one_mul] at h1
        exact h1
      have hτ1 : τ = 1 := by
        ext x
        rw [mem_Ine] at hτA
        have h := hτA.2 x ((Av.valuation_le_one_iff x).2 (hall x))
        rw [valuation_lt_one_iff_zero_or_inv_not_mem] at h
        rcases h with h | h
        · simpa [sub_eq_zero] using h
        · exact absurd (hall _) h
      have : (⟨π τ, hτ⟩ : Φ.G0) = 1 := by
        apply Subtype.ext
        simp [hτ1]
      rw [this, map_one]
    · haveI : P.IsPrime := Ideal.comap_isPrime φ (IsLocalRing.maximalIdeal Av)
      let v : HeightOneSpectrum (𝓞 F) := ⟨P, inferInstance, hPb⟩
      have hA : IsPlaceOver Av v := fun x => (hP x).symm
      by_cases hvS : v ∈ S
      · have hlv : (l : 𝓞 F) ∈ v.asIdeal := hL.only v hvS
        obtain ⟨u, hu⟩ := (hL.loc.mem v).2 hlv
        have hAu : IsPlaceOver Av (pl u) := hu ▸ hA
        obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hL.loc.isOver u) hAu
        rw [← hσ] at hτA
        have hc := conj_mem_inertia_of_mem_inertia_smul (A u) σ τ hτA
        have hdec : σ⁻¹ * τ * σ ∈ (ι u).range := by
          rw [hL.loc.range u]
          exact Ine_le_Dec _ hc
        obtain ⟨s, hs⟩ := hdec
        have hsI : s ∈ Φ.Iv u := by
          rw [hL.ine u, Subgroup.mem_comap, hs]
          exact hc
        have hπτ : π τ = π σ * ((Φ.loc0 u s : Φ.G0) : Φ.Γ) * (π σ)⁻¹ := by
          have h1 : ((Φ.loc0 u s : Φ.G0) : Φ.Γ) = π (ι u s) := hL.loc_eq u s
          rw [h1, hs, map_mul, map_mul, map_inv]
          group
        rcases Int.units_eq_one_or (Φ.del (π σ)) with hd | hd
        · have ha : π σ ∈ Φ.del.ker := hd
          have : (⟨π τ, hτ⟩ : Φ.G0) = ⟨π σ, ha⟩ * Φ.loc0 u s * (⟨π σ, ha⟩ : Φ.G0)⁻¹ := by
            apply Subtype.ext
            simp [hπτ]
          rw [this, map_mul, map_mul, map_inv, mul_comm (χ _), mul_inv_cancel_right]
          have h := hχI (u, false) s hsI
          simpa [UpperTheory.V.Fr.Frame.loc2] using h
        · have ha : Φ.c⁻¹ * π σ ∈ Φ.del.ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hd, hL.del_c]
            rfl
          have : (⟨π τ, hτ⟩ : Φ.G0) =
              Φ.conj (⟨Φ.c⁻¹ * π σ, ha⟩ * Φ.loc0 u s * (⟨Φ.c⁻¹ * π σ, ha⟩ : Φ.G0)⁻¹) := by
            apply Subtype.ext
            simp only [UpperTheory.V.Fr.Frame.conj, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]
            simp [hπτ]
            group
          rw [this, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, mul_comm (χ _),
            mul_inv_cancel_right]
          have h := hχI (u, true) s hsI
          simpa [UpperTheory.V.Fr.Frame.loc2] using h
      · haveI := hL.g.normal
        set n := K.index with hn
        have hK : τ ^ n ∈ K := K.pow_index_mem τ
        have hI : τ ^ n ∈ Ine Av := (Ine Av).pow_mem hτA n
        have hT : τ ^ n ∈ tameN (↑S) K := by
          apply Subgroup.le_topologicalClosure
          apply Subgroup.subset_normalClosure
          refine Set.mem_iUnion₂.2 ⟨v, by simpa using hvS, Set.mem_iUnion₂.2 ⟨Av, hA, ?_⟩⟩
          exact Subgroup.mem_inf.2 ⟨hI, hK⟩
        have hπ : π (τ ^ n) = 1 := by
          rw [← MonoidHom.mem_ker, hL.g.ker]
          exact hT
        apply eq_one_of_pow_coprime_in_pGroup (Fact.out : l.Prime) hB _ n hL.g.idx
        rw [← map_pow]
        have : (⟨π τ, hτ⟩ : Φ.G0) ^ n = 1 := by
          apply Subtype.ext
          simp [← map_pow, hπ]
        rw [this, map_one]
  have hopen : IsOpen (ψ.ker : Set (G E Ω)) := by
    have hc : Continuous f := by
      have h1 : Continuous (UpperTheory.V.Base.galEmb F E Ω) :=
        (UpperTheory.V.Base.galEmbTop F E Ω).1.continuous
      exact (hL.g.cont.comp h1).subtype_mk _
    have h2 : IsOpen ((χ.comp f).ker : Set (G E Ω)) := hχo.preimage hc
    refine Subgroup.isOpen_mono ?_ h2
    intro x hx
    simp only [MonoidHom.mem_ker] at hx ⊢
    simp [ψ, hx]
  have hine : ∀ Av : ValuationSubring Ω, Ine Av ≤ ψ.ker := by
    intro Av σ hσ
    have h := key Av _ (galEmb_mem_inertia F E Ω Av σ hσ) (hmemU σ)
    rw [MonoidHom.mem_ker]
    have : ψ σ = χ ⟨π (UpperTheory.V.Base.galEmb F E Ω σ), hmemU σ⟩ ^ 2 := rfl
    rw [this, h, one_pow]
  have hconj : ∀ σ : G E Ω, IsConjOm σ.toRingEquiv → ψ σ = 1 := by
    intro σ ⟨j, hj⟩
    have hsq : σ * σ = 1 := by
      ext x
      apply j.injective
      simp only [AlgEquiv.mul_apply, AlgEquiv.one_apply]
      have := hj (σ x)
      simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_toEquiv, AlgEquiv.coe_ringEquiv] at this hj
      rw [this, hj, Complex.conj_conj]
    have : ψ σ = χ (f (σ * σ)) := by
      simp [ψ, pow_two]
    rw [this, hsq, map_one, map_one]
  have hker := UpperTheory.V.Kum.artKer E Ω B ψ hopen hine hconj
  obtain ⟨τ, hτ⟩ := hL.g.onto (g : Φ.Γ)
  have hτU : τ ∈ UpperTheory.V.Base.galOf F E Ω := by
    rw [hgal]
    show π τ ∈ Φ.del.ker
    rw [hτ]
    exact g.2
  let σ : G E Ω := { τ with commutes' := fun x => hτU x }
  have hσ : f σ = g := by
    apply Subtype.ext
    show π (UpperTheory.V.Base.galEmb F E Ω σ) = g
    rw [← hτ]
    congr 1
  have h1 : ψ (σ ^ Nat.card (ClassGroup (𝓞 E))) = 1 := by
    apply hker
    rw [MonoidHom.mem_ker, map_pow]
    exact pow_card_eq_one'
  rw [map_pow] at h1
  have h2 : ψ σ = χ g ^ 2 := by
    simp [ψ, hσ]
  rw [h2, ← pow_mul] at h1
  exact h1
