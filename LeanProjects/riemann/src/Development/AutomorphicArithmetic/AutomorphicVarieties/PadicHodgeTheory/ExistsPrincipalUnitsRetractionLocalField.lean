import GroundTheory.LocalFields.PrincipalUnitsRank

open GroundTheory.LocalField ValuativeRel Module Topology

private theorem UpperTheory.exists_continuous_retraction_power {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (u : G →* G) (m : ℕ)
    (hfix : ∀ x ∈ U, u x = x) (hm : ∀ y, u y ^ m ∈ U) (s : U →* U) (hs : ∀ x, s x ^ m = x) :
    ∃ r : G →* U, Continuous r ∧ (∀ x : U, r x = x) ∧ ∀ y, (r y : G) ^ m = u y ^ m := by
  let r : G →* U :=
    { toFun := fun y => s ⟨u y ^ m, hm y⟩
      map_one' := by
        have h : (⟨u 1 ^ m, hm 1⟩ : U) = 1 := by ext; simp
        rw [h, map_one]
      map_mul' := by
        intro x y
        have h : (⟨u (x * y) ^ m, hm (x * y)⟩ : U) = ⟨u x ^ m, hm x⟩ * ⟨u y ^ m, hm y⟩ := by
          ext; simp [mul_pow]
        rw [h, map_mul] }
  have hr : ∀ y, r y = s ⟨u y ^ m, hm y⟩ := fun y => rfl
  have hfixr : ∀ x : U, r x = x := by
    intro x
    have h : (⟨u x ^ m, hm x⟩ : U) = x ^ m := by ext; simp [hfix x x.2]
    rw [hr, h, map_pow, hs]
  refine ⟨r, ?_, hfixr, ?_⟩
  · rw [continuous_induced_rng]
    let f : G →* G := U.subtype.comp r
    have hf : ∀ y, f y = (r y : G) := fun y => rfl
    have hc : Continuous f := by
      apply continuous_of_continuousAt_one f
      apply continuousAt_id.congr
      filter_upwards [hU.mem_nhds U.one_mem] with x hx
      rw [hf, show x = ((⟨x, hx⟩ : U) : G) from rfl, hfixr]
      rfl
    exact hc
  · intro y
    rw [hr, ← Subgroup.coe_pow, hs]

theorem UpperTheory.exists_principal_units_retraction_localField :
    ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (l : ℕ) [Fact l.Prime] [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) l], (∀ y ∈ CommGroup.primaryComponent Kˣ l, y ∈ GroundTheory.LocalField.unitFiltrationUnits K 1) ∧ ∃ r : Kˣ →* ↥(GroundTheory.LocalField.unitFiltrationUnits K 1), Continuous r ∧ (∀ u : ↥(GroundTheory.LocalField.unitFiltrationUnits K 1), r u = u) ∧ ∀ (n : ℕ) (y : Kˣ), (l : ℤ) ^ n ∣ GroundTheory.LocalField.ord (y : K) → (∃ w, r y = w ^ l ^ n) → ∃ z : Kˣ, y = z ^ l ^ n := by
  intro K _ _ _ _ l _ _
  have hl : l.Prime := Fact.out
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥𝒪[K]
  haveI : Fintype 𝓀[K] := Fintype.ofFinite _
  have hq : l ∣ Nat.card 𝓀[K] := by
    rw [← CharP.cast_eq_zero_iff 𝓀[K] l, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero 𝓀[K]
  have hq1 : 1 ≤ Nat.card 𝓀[K] := Nat.card_pos
  have hcop : Nat.Coprime (Nat.card 𝓀[K] - 1) l := by
    rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
    intro h
    have h2 := Nat.dvd_sub hq h
    rw [show Nat.card 𝓀[K] - (Nat.card 𝓀[K] - 1) = 1 by omega] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.mp h2)
  have bez : ∀ {M : Type} [CommGroup M] (t : M) (a b : ℕ), Nat.Coprime a b →
      ∃ A B : ℤ, t = (t ^ a) ^ A * (t ^ b) ^ B := by
    intro M _ t a b h
    refine ⟨Nat.gcdA a b, Nat.gcdB a b, ?_⟩
    have h' : (a : ℤ) * Nat.gcdA a b + b * Nat.gcdB a b = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, h, Nat.cast_one]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, h', zpow_one]
  have hidx : ∀ v : (𝒪[K])ˣ, v ^ (Nat.card 𝓀[K] - 1) ∈ unitFiltration K 1 := by
    intro v
    rw [← index_unitFiltration_one]
    exact Subgroup.pow_index_mem _ v
  have hdecomp : ∀ y : Kˣ,
      y = uniformizerUnit hϖ ^ ord (y : K) * unitsIncl K ((unitsEquivIntProd hϖ) y).2 := by
    intro y
    apply (unitsEquivIntProd hϖ).injective
    rw [map_mul, map_zpow, unitsEquivIntProd_uniformizer, unitsEquivIntProd_unitsIncl]
    ext
    · simp [unitsEquivIntProd_fst, ← ofAdd_zsmul]
    · simp
  have hinj : ∀ w : (𝒪[K])ˣ, unitsIncl K w = 1 → w = 1 := by
    intro w hw
    have h := congrArg (fun z => ((unitsEquivIntProd hϖ) z).2) hw
    simpa [unitsEquivIntProd_unitsIncl] using h
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.mp hy
    have hord : ord (y : K) = 0 := by
      have h := congrArg (fun z => ((unitsEquivIntProd hϖ) z).1) hk
      simp only [map_pow, Prod.pow_fst, map_one, Prod.fst_one, unitsEquivIntProd_fst] at h
      rw [← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h (by exact_mod_cast pow_ne_zero k hl.ne_zero)
      · exact h
    set v := ((unitsEquivIntProd hϖ) y).2 with hvdef
    have hyv : y = unitsIncl K v := by
      conv_lhs => rw [hdecomp y]
      rw [hord, zpow_zero, one_mul]
    have hvk : v ^ l ^ k = 1 := by
      apply hinj
      rw [map_pow, ← hyv, hk]
    obtain ⟨A, B, hAB⟩ := bez v (Nat.card 𝓀[K] - 1) (l ^ k) (Nat.Coprime.pow_right k hcop)
    have hv : v ∈ unitFiltration K 1 := by
      rw [hAB, hvk, one_zpow, mul_one]
      exact zpow_mem (hidx v) A
    rw [hyv]
    exact Subgroup.mem_map_of_mem _ hv
  · let u : Kˣ →* Kˣ :=
      (unitsIncl K).comp ((MonoidHom.snd _ _).comp (unitsEquivIntProd hϖ).toMonoidHom)
    have hu : ∀ y, u y = unitsIncl K ((unitsEquivIntProd hϖ) y).2 := fun y => rfl
    have hunit : IsUnit ((Nat.card 𝓀[K] - 1 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      apply le_antisymm (PadicInt.norm_le_one _)
      by_contra hlt
      push_neg at hlt
      have h : l ∣ Fintype.card 𝓀[K] - 1 := by simpa using hlt
      rw [← Nat.card_eq_fintype_card] at h
      exact (hl.coprime_iff_not_dvd.mp hcop.symm) h
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[l], ((Nat.card 𝓀[K] - 1 : ℕ) : ℤ_[l]) * c = 1 :=
      ⟨_, hunit.mul_val_inv⟩
    let s : unitFiltrationUnits K 1 →* unitFiltrationUnits K 1 :=
      { toFun := fun x => Additive.toMul (c • Additive.ofMul x)
        map_one' := by simp
        map_mul' := by intro x y; simp [smul_add] }
    have hs : ∀ x, s x ^ (Nat.card 𝓀[K] - 1) = x := by
      intro x
      show (Additive.toMul (c • Additive.ofMul x)) ^ (Nat.card 𝓀[K] - 1) = x
      rw [← toMul_nsmul, ← natCast_smul l, smul_smul, hc, one_smul]
      rfl
    have hm : ∀ y, u y ^ (Nat.card 𝓀[K] - 1) ∈ unitFiltrationUnits K 1 := by
      intro y
      rw [hu, ← map_pow]
      exact Subgroup.mem_map_of_mem _ (hidx _)
    have hfix : ∀ x ∈ unitFiltrationUnits K 1, u x = x := by
      intro x hx
      obtain ⟨v, _, rfl⟩ := Subgroup.mem_map.mp hx
      rw [hu, unitsEquivIntProd_unitsIncl]
    obtain ⟨r, hrc, hrfix, hrpow⟩ := UpperTheory.exists_continuous_retraction_power _ (isOpen_unitFiltrationUnits 1) u
      (Nat.card 𝓀[K] - 1) hfix hm s hs
    refine ⟨r, hrc, hrfix, ?_⟩
    rintro n y ⟨a, ha⟩ ⟨w, hw⟩
    set t := u y * (r y : Kˣ)⁻¹ with htdef
    have ht : t ^ (Nat.card 𝓀[K] - 1) = 1 := by
      rw [htdef, mul_pow, inv_pow, hrpow, mul_inv_cancel]
    obtain ⟨A, B, hAB⟩ := bez t (Nat.card 𝓀[K] - 1) (l ^ n) (Nat.Coprime.pow_right n hcop)
    rw [ht, one_zpow, one_mul] at hAB
    have hry : (r y : Kˣ) = (w : Kˣ) ^ (l ^ n) := by rw [hw]; rfl
    have e1 : (uniformizerUnit hϖ ^ a) ^ (l ^ n) = uniformizerUnit hϖ ^ ord (y : K) := by
      rw [ha, ← zpow_natCast, ← zpow_mul, mul_comm]
      push_cast
      rfl
    have e2 : (t ^ B) ^ (l ^ n) = t := by
      conv_rhs => rw [hAB]
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    refine ⟨uniformizerUnit hϖ ^ a * t ^ B * (w : Kˣ), ?_⟩
    rw [mul_pow, mul_pow, e1, e2, ← hry, htdef, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, hu]
    exact hdecomp y
