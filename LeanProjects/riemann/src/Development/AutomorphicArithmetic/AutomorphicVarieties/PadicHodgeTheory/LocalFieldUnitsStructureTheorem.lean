import GroundTheory.LocalFields.PrincipalUnitsRank
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteZpModuleTorsionFreeSplitting
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsPrincipalUnitsRetractionLocalField

open GroundTheory.LocalField ValuativeRel Module Topology

private theorem UpperTheory.mem_torsion_iff_primary_component (l : ℕ) [hl : Fact l.Prime] {G : Type} [CommGroup G]
    (U : Subgroup G) [Module ℤ_[l] (Additive U)] (x : Additive U) :
    x ∈ Submodule.torsion ℤ_[l] (Additive U) ↔
      ((Additive.toMul x : U) : G) ∈ CommGroup.primaryComponent G l := by
  have key : ∀ m : ℕ, ((Additive.toMul x : U) : G) ^ m = 1 ↔ m • x = 0 := by
    intro m
    rw [← Subgroup.coe_pow, ← toMul_nsmul, OneMemClass.coe_eq_one, toMul_eq_one]
  rw [Submodule.mem_torsion_iff, CommGroup.mem_primaryComponent]
  constructor
  · rintro ⟨a, ha⟩
    have ha0 : (a : ℤ_[l]) ≠ 0 := nonZeroDivisors.coe_ne_zero a
    have hspec := PadicInt.unitCoeff_spec ha0
    set c := PadicInt.unitCoeff ha0
    set v := (a : ℤ_[l]).valuation
    have hax : (a : ℤ_[l]) • x = 0 := ha
    rw [hspec, mul_smul] at hax
    have hlv : ((l : ℤ_[l]) ^ v) • x = 0 := by
      have := congrArg (fun y => ((c⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • y) hax
      simpa [smul_smul] using this
    refine ⟨v, (key _).2 ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    push_cast
    exact hlv
  · rintro ⟨k, hk⟩
    refine ⟨⟨((l ^ k : ℕ) : ℤ_[l]), mem_nonZeroDivisors_of_ne_zero ?_⟩, ?_⟩
    · exact_mod_cast pow_ne_zero k hl.out.ne_zero
    · show ((l ^ k : ℕ) : ℤ_[l]) • x = 0
      rw [Nat.cast_smul_eq_nsmul]
      exact (key _).1 hk

private theorem UpperTheory.finite_quotient_of_retraction_rank (l : ℕ) [hl : Fact l.Prime] {G : Type} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (U : Subgroup G) [Module ℤ_[l] (Additive U)] [ContinuousSMul ℤ_[l] (Additive U)]
    [Module.Finite ℤ_[l] (Additive U)] (hP : ∀ y ∈ CommGroup.primaryComponent G l, y ∈ U)
    (r : G →* U) (hr : Continuous r) (hid : ∀ u : U, r u = u) (d : ℕ)
    (hd : Module.finrank ℤ_[l] (Additive U) = d) :
    Finite ↥(CommGroup.primaryComponent G l) ∧
    ∃ (p : G →* Multiplicative (Fin d → ℤ_[l])) (t : G →* ↥(CommGroup.primaryComponent G l)),
      Continuous p ∧ IsOpen (t.ker : Set G) ∧
      (∀ y : ↥(CommGroup.primaryComponent G l), p y = 1 ∧ t y = y) ∧
      (∀ x τ, ∃ y ∈ U, p y = x ∧ t y = τ) ∧
      ∀ (n : ℕ) (y : G), (∀ i, (l : ℤ_[l]) ^ n ∣ Multiplicative.toAdd (p y) i) → t y = 1 →
        ∃ w, r y = w ^ l ^ n := by
  subst hd
  haveI : T2Space (Additive U) := inferInstanceAs (T2Space U)
  obtain ⟨hfin, p0, t0, hp0c, ht0o, hpt, hbij⟩ := UpperTheory.finite_zp_module_torsion_free_splitting l (Additive U)
  have memT : ∀ u : U, (u : G) ∈ CommGroup.primaryComponent G l →
      Additive.ofMul u ∈ Submodule.torsion ℤ_[l] (Additive U) := fun u hu =>
    (UpperTheory.mem_torsion_iff_primary_component l U (Additive.ofMul u)).2 hu
  have memP : ∀ z : Submodule.torsion ℤ_[l] (Additive U),
      ((Additive.toMul (z : Additive U) : U) : G) ∈ CommGroup.primaryComponent G l := fun z =>
    (UpperTheory.mem_torsion_iff_primary_component l U z).1 z.2
  let p : G →* Multiplicative (Fin (Module.finrank ℤ_[l] (Additive U)) → ℤ_[l]) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (p0 (Additive.ofMul (r g)))) (by
      intro a b
      simp [ofAdd_add])
  let t : G →* CommGroup.primaryComponent G l :=
    MonoidHom.mk' (fun g => ⟨((Additive.toMul (t0 (Additive.ofMul (r g)) : Additive U) : U) : G),
      memP _⟩) (by
      intro a b
      apply Subtype.ext
      simp)
  have hrU : ∀ y : CommGroup.primaryComponent G l, r (y : G) = ⟨y, hP y y.2⟩ :=
    fun y => hid ⟨y, hP y y.2⟩
  have htker : ∀ g, t g = 1 ↔ t0 (Additive.ofMul (r g)) = 0 := by
    intro g
    rw [← OneMemClass.coe_eq_one]
    show ((Additive.toMul (t0 (Additive.ofMul (r g)) : Additive U) : U) : G) = 1 ↔ _
    rw [OneMemClass.coe_eq_one, toMul_eq_one, ZeroMemClass.coe_eq_zero]
  refine ⟨?_, p, t, ?_, ?_, ?_, ?_, ?_⟩
  · haveI := hfin
    refine Finite.of_injective (β := Submodule.torsion ℤ_[l] (Additive U))
      (fun y => ⟨Additive.ofMul ⟨(y : G), hP y y.2⟩, memT _ y.2⟩) ?_
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun z : Submodule.torsion ℤ_[l] (Additive U) =>
      ((Additive.toMul (z : Additive U) : U) : G)) hab
    simpa using this
  · exact continuous_ofAdd.comp (hp0c.comp (continuous_ofMul.comp hr))
  · have hset : (t.ker : Set G) = (fun g => Additive.ofMul (r g)) ⁻¹' (t0.ker : Set (Additive U)) := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, LinearMap.mem_ker, Set.mem_preimage]
      exact htker g
    rw [hset]
    exact ht0o.preimage (continuous_ofMul.comp hr)
  · intro y
    have hz := hpt ⟨Additive.ofMul ⟨(y : G), hP y y.2⟩, memT _ y.2⟩
    have hry := hrU y
    constructor
    · show Multiplicative.ofAdd (p0 (Additive.ofMul (r y))) = 1
      rw [hry, hz.1]
      rfl
    · apply Subtype.ext
      show ((Additive.toMul (t0 (Additive.ofMul (r y)) : Additive U) : U) : G) = y
      rw [hry, hz.2]
      rfl
  · intro x τ
    obtain ⟨m, hm⟩ := hbij.2 (Multiplicative.toAdd x, ⟨Additive.ofMul ⟨(τ : G), hP τ τ.2⟩, memT _ τ.2⟩)
    simp only [Prod.mk.injEq] at hm
    refine ⟨((Additive.toMul m : U) : G), (Additive.toMul m).2, ?_, ?_⟩
    · show Multiplicative.ofAdd (p0 (Additive.ofMul (r _))) = x
      rw [hid, ofMul_toMul, hm.1, ofAdd_toAdd]
    · apply Subtype.ext
      show ((Additive.toMul (t0 (Additive.ofMul (r _)) : Additive U) : U) : G) = τ
      rw [hid, ofMul_toMul, hm.2]
      rfl
  · intro n y hdiv hty
    have ht0 : t0 (Additive.ofMul (r y)) = 0 := (htker y).1 hty
    choose c hc using hdiv
    obtain ⟨m', hm'⟩ := hbij.2 (c, 0)
    simp only [Prod.mk.injEq] at hm'
    have heq : Additive.ofMul (r y) = ((l : ℤ_[l]) ^ n) • m' := by
      apply hbij.1
      simp only [Prod.mk.injEq, map_smul, hm'.1, hm'.2, smul_zero, ht0, and_true]
      funext i
      rw [Pi.smul_apply, smul_eq_mul, ← hc i]
      rfl
    refine ⟨Additive.toMul m', ?_⟩
    have hsm : ((l : ℤ_[l]) ^ n) • m' = (l ^ n) • m' := by
      rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
      push_cast
      rfl
    rw [← toMul_ofMul (r y), heq, hsm, toMul_nsmul]

theorem UpperTheory.localField_units_structure_theorem :
    ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [ValuativeExtension ℚ_[l] K] [FiniteDimensional ℚ_[l] K], Finite ↥(CommGroup.primaryComponent Kˣ l) ∧ ∃ (p : Kˣ →* Multiplicative (Fin (Module.finrank ℚ_[l] K) → ℤ_[l])) (t : Kˣ →* ↥(CommGroup.primaryComponent Kˣ l)), Continuous p ∧ IsOpen (t.ker : Set Kˣ) ∧ (∀ y : ↥(CommGroup.primaryComponent Kˣ l), p y = 1 ∧ t y = y) ∧ (∀ x τ, ∃ y : Kˣ, GroundTheory.LocalField.ord (y : K) = 0 ∧ p y = x ∧ t y = τ) ∧ ∀ (n : ℕ) (y : Kˣ), (∀ i, (l : ℤ_[l]) ^ n ∣ Multiplicative.toAdd (p y) i) → (l : ℤ) ^ n ∣ GroundTheory.LocalField.ord (y : K) → t y = 1 → ∃ z : Kˣ, y = z ^ l ^ n := by
  intro K _ _ _ _ l _ _ _ _
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hlmax : (l : 𝒪[K]) ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hinv : (algebraMap ℚ_[l] K) ((l : ℚ_[l])⁻¹) ∈ 𝒪[K] := by
      have heq : (algebraMap ℚ_[l] K) ((l : ℚ_[l])⁻¹) = (v : K) := by
        have h1 : ((l : 𝒪[K]) : K) * (v : K) = 1 := by
          have := congrArg (fun z : 𝒪[K] => (z : K)) hv
          simpa using this
        rw [map_inv₀, map_natCast]
        push_cast at h1
        exact inv_eq_of_mul_eq_one_right h1
      rw [heq]
      exact v.2
    rw [algebraMap_mem_integer_iff, PadicRank.mem_integer_padic_iff, norm_inv, Padic.norm_p,
      inv_inv] at hinv
    have h2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
    linarith
  haveI : CharP 𝓀[K] l := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
    have := (IsLocalRing.residue_eq_zero_iff _).2 hlmax
    simpa using this
  have hhom : CharZero.padicHom K l = algebraMap ℚ_[l] K := by
    have := (Padic.denseRange_ratCast (p := l)).equalizer (CharZero.continuous_padicHom K l)
      (GroundTheory.LocalField.continuous_algebraMap ℚ_[l] K) (by funext q; simp)
    exact RingHom.ext (congrFun this)
  have halg : (CharZero.padicHom K l).toAlgebra = ‹Algebra ℚ_[l] K› :=
    Algebra.algebra_ext _ _ fun q => by
      show CharZero.padicHom K l q = algebraMap ℚ_[l] K q
      rw [hhom]
  have hfr : Module.finrank ℤ_[l] (Additive (unitFiltrationUnits K 1)) = Module.finrank ℚ_[l] K := by
    have := finrank_principalUnits (K := K) l
    rw [halg] at this
    exact this
  haveI := finite_principalUnits (K := K) l
  obtain ⟨hPU, r, hr, hid, hdiv⟩ := UpperTheory.exists_principal_units_retraction_localField K l
  obtain ⟨hfin, p, t, hp, ht, hpt, hsurj, hpow⟩ := UpperTheory.finite_quotient_of_retraction_rank l (unitFiltrationUnits K 1) hPU r hr
    hid (Module.finrank ℚ_[l] K) hfr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hord : ∀ y ∈ unitFiltrationUnits K 1, ord (y : K) = 0 := by
    intro y hy
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.1 hy
    have h1 := unitsEquivIntProd_fst hϖ (unitsIncl K u)
    rw [unitsEquivIntProd_unitsIncl] at h1
    have h2 : Multiplicative.ofAdd (ord ((unitsIncl K u : Kˣ) : K)) = Multiplicative.ofAdd 0 := by
      rw [← h1]
      rfl
    exact Multiplicative.ofAdd.injective h2
  refine ⟨hfin, p, t, hp, ht, hpt, ?_, ?_⟩
  · intro x τ
    obtain ⟨y, hy, hpx, hty⟩ := hsurj x τ
    exact ⟨y, hord y hy, hpx, hty⟩
  · intro n y hpd hod hty
    exact hdiv n y hod (hpow n y hpd hty)
