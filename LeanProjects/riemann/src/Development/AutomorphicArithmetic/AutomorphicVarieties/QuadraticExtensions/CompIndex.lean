import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbBasic
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.GalCharBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LevChar

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem exists_isPrimitiveRoot_of_isAlgClosure_rat (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) [NeZero n] :
    ∃ ω : Ω, IsPrimitiveRoot ω n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω n

private theorem coe_galChar_eq_natCast_of_apply_eq_pow (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) [NeZero n]
    (σ : G ℚ Ω) (ω : Ω) (hω : IsPrimitiveRoot ω n) (c : ℕ) (hc : σ ω = ω ^ c) :
    ((galChar Ω n σ : (ZMod n)ˣ) : ZMod n) = (c : ZMod n) := by
  have hc' : σ ω = ω ^ (c % n) := by
    rw [hc]
    conv_lhs => rw [← Nat.mod_add_div c n, pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have htn : (t : Ω) ^ n = 1 := by
    rw [mem_rootsOfUnity] at ht
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  obtain ⟨i, -, hi⟩ := hω.eq_pow_of_pow_eq_one htn
  rw [← hi, ZMod.val_natCast]
  change σ (ω ^ i) = _
  rw [map_pow, hc', ← pow_mul, ← pow_mul, mul_comm]

private theorem apply_eq_pow_val_galChar_of_isPrimitiveRoot (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) [NeZero n]
    (σ : G ℚ Ω) (ω : Ω) (hω : IsPrimitiveRoot ω n) :
    σ ω = ω ^ ((galChar Ω n σ : (ZMod n)ˣ) : ZMod n).val := by
  have := modularCyclotomicCharacter.spec Ω (n := n) (by
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : CharZero Ω := algebraRat.charZero Ω
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω n) σ.toRingEquiv (t := (hω.toRootsOfUnity : Ωˣ)) (SetLike.coe_mem _)
  simp only [IsPrimitiveRoot.val_toRootsOfUnity_coe, Units.val_pow_eq_pow_val] at this
  exact this

private theorem coe_galChar_eq_val_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (k m : ℕ) [NeZero k] [NeZero m]
    (hkm : k ∣ m) (σ : G ℚ Ω) :
    ((galChar Ω k σ : (ZMod k)ˣ) : ZMod k) = (((galChar Ω m σ : (ZMod m)ˣ) : ZMod m).val : ZMod k) := by
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_of_isAlgClosure_rat Ω m
  obtain ⟨r, hr⟩ := hkm
  have hω' : IsPrimitiveRoot (ω ^ r) k := hω.pow (Nat.pos_of_neZero m) (by rw [hr, mul_comm])
  apply coe_galChar_eq_natCast_of_apply_eq_pow Ω k σ _ hω'
  rw [map_pow, apply_eq_pow_val_galChar_of_isPrimitiveRoot Ω m σ ω hω, ← pow_mul, ← pow_mul, mul_comm]

private theorem unitsMap_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (k m : ℕ) [NeZero k] [NeZero m]
    (hkm : k ∣ m) (σ : G ℚ Ω) :
    ZMod.unitsMap hkm (galChar Ω m σ) = galChar Ω k σ := by
  ext
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, coe_galChar_eq_val_galChar_of_dvd Ω k m hkm σ]

private theorem mem_comap_cycZ_princ_two_iff_galChar_eq_one (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (σ : G ℚ Ω) :
    σ ∈ Subgroup.comap (cycZ ℚ Ω 2) (KStar.TotallyRealRoots.princ 2 n) ↔ galChar Ω (2 ^ n) σ = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (2 ^ i) := fun i => inferInstance
  rw [Subgroup.mem_comap, KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow, Units.ext_iff, Units.ext_iff]
  change PadicInt.toZModPow n ((cyclotomicCharacter Ω 2 σ.toRingEquiv : ℤ_[2]ˣ) : ℤ_[2]) = 1 ↔ _
  rw [cyclotomicCharacter.toZModPow]
  rfl

private theorem mem_galOf_iff_val_galChar_of_fixes_iff (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (E : Type) [Field E]
    [NumberField E] [Algebra E Ω] (N : ℕ) [NeZero N] (j : E →ₐ[ℚ] CyclotomicField N ℚ)
    (ζ : CyclotomicField N ℚ) (hζ : IsPrimitiveRoot ζ N) (Q : ℕ → Prop)
    (hQ : ∀ (τ : Gal(CyclotomicField N ℚ/ℚ)) (a : ℕ), τ ζ = ζ ^ a → ((∀ x, τ (j x) = j x) ↔ Q a))
    (σ : G ℚ Ω) : σ ∈ galOf ℚ E Ω ↔ Q ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hce0 := CyclotomicField.isCyclotomicExtension N ℚ
  have hce : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := by exact hce0
  haveI : IsGalois ℚ (CyclotomicField N ℚ) := by
    exact IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
  let ι : CyclotomicField N ℚ →ₐ[ℚ] Ω := IsAlgClosed.lift
  letI : Algebra (CyclotomicField N ℚ) Ω := ι.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField N ℚ) Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => (ι.commutes x).symm)
  haveI : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [eq_ratCast, eq_ratCast, map_ratCast])
  let φ := (ι.comp j).liftNormal Ω
  let ρ : G ℚ Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
  have hρ : ∀ x : E, ρ (algebraMap E Ω x) = ι (j x) := fun x => (ι.comp j).liftNormal_commutes Ω x
  let σ' : G ℚ Ω := ρ * σ * ρ⁻¹
  have hgal : galChar Ω N σ' = galChar Ω N σ := by
    simp only [σ', map_mul, map_inv]
    rw [mul_comm (galChar Ω N ρ), mul_assoc, mul_inv_cancel, mul_one]
  let τ : Gal(CyclotomicField N ℚ/ℚ) := σ'.restrictNormal (CyclotomicField N ℚ)
  have hτ : ∀ y, ι (τ y) = σ' (ι y) := fun y => AlgEquiv.restrictNormal_commutes σ' (CyclotomicField N ℚ) y
  have hτζ : τ ζ = ζ ^ ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
    apply ι.toRingHom.injective
    change ι (τ ζ) = ι (ζ ^ _)
    rw [hτ, map_pow, apply_eq_pow_val_galChar_of_isPrimitiveRoot Ω N σ' (ι ζ) (hζ.map_of_injective ι.toRingHom.injective), hgal]
  rw [← hQ τ _ hτζ, mem_galOf]
  apply forall_congr'
  intro x
  rw [← ι.toRingHom.injective.eq_iff]
  change _ ↔ ι (τ (j x)) = ι (j x)
  rw [hτ, ← hρ x]
  simp only [σ', AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  exact ρ.injective.eq_iff.symm

private theorem zmod_unit_mem_squares_iff_jacobiSym_eq_one_of_prime (p m : ℕ) (hp : p.Prime) (hm : m = p) (a : ℕ) (u : (ZMod m)ˣ)
    (hu : (u : ZMod m) = a) :
    u ∈ (powMonoidHom 2 : (ZMod m)ˣ →* (ZMod m)ˣ).range ↔ jacobiSym (a : ℤ) p = 1 := by
  subst hm
  haveI : Fact m.Prime := ⟨hp⟩
  have ha0 : (((a : ℤ)) : ZMod m) ≠ 0 := by
    rw [Int.cast_natCast, ← hu]
    exact u.ne_zero
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff m ha0, Int.cast_natCast, ← hu,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, by simp [pow_two]⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by simpa using hr)
    refine ⟨Units.mk0 r hr0, ?_⟩
    ext
    simp [pow_two, hr]

private theorem mem_abU_sup_iff (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A B : AbF) (σ : G ℚ Ω) :
    σ ∈ abU Ω (A.sup B) ↔ σ ∈ abU Ω A ∧ σ ∈ abU Ω B := by
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : NeZero B.m := ⟨B.pos.ne'⟩
  haveI : NeZero (A.sup B).m := ⟨(A.sup B).pos.ne'⟩
  have h1 : A.m ∣ (A.sup B).m := Dvd.intro B.m rfl
  have h2 : B.m ∣ (A.sup B).m := Dvd.intro_left A.m rfl
  have e1 := unitsMap_galChar_of_dvd Ω A.m (A.sup B).m h1 σ
  have e2 := unitsMap_galChar_of_dvd Ω B.m (A.sup B).m h2 σ
  change (ZMod.unitsMap h1 (galChar Ω (A.sup B).m σ) ∈ A.H ∧
    ZMod.unitsMap h2 (galChar Ω (A.sup B).m σ) ∈ B.H) ↔
    (galChar Ω A.m σ ∈ A.H ∧ galChar Ω B.m σ ∈ B.H)
  rw [e1, e2]

theorem UpperTheory.V.Two.compIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (e q d : ℕ) (E : Type) [Field E] [NumberField E] [Algebra E Ω], q.Prime → d.Prime → IsCompField M e q d E →
      levU 2 (abU Ω (base2 M q d)) (e + 2) ≤ galOf ℚ E Ω ∧ (levU 2 (abU Ω (base2 M q d)) (e + 2)).relIndex (galOf ℚ E Ω) ∣ 2 := by
  intro Ω _ _ _ M e q d E _ _ _ hq hd hE
  obtain ⟨N, hN, j, ζ, h2N, hMN, hqN, hdN, hζ, hτ⟩ := hE
  haveI := hN
  haveI : NeZero M.m := ⟨M.pos.ne'⟩
  haveI : NeZero (AbF.cyc 4).m := ⟨(AbF.cyc 4).pos.ne'⟩
  haveI : NeZero (AbF.quad q).m := ⟨(AbF.quad q).pos.ne'⟩
  haveI : NeZero (AbF.quad d).m := ⟨(AbF.quad d).pos.ne'⟩
  haveI : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  have hqm : (AbF.quad q).m = q := max_eq_left hq.one_lt.le
  have hdm : (AbF.quad d).m = d := max_eq_left hd.one_lt.le
  have h4m : (AbF.cyc 4).m = 4 := rfl
  have key := fun σ => mem_galOf_iff_val_galChar_of_fixes_iff Ω E N j ζ hζ _ hτ σ
  have hlev : ∀ σ : G ℚ Ω, σ ∈ levU 2 (abU Ω (base2 M q d)) (e + 2) ↔
      ((galChar Ω M.m σ ∈ M.H ∧ galChar Ω (AbF.cyc 4).m σ ∈ (AbF.cyc 4).H) ∧
        galChar Ω (AbF.quad q).m σ ∈ (AbF.quad q).H ∧ galChar Ω (AbF.quad d).m σ ∈ (AbF.quad d).H) ∧
        galChar Ω (2 ^ (e + 2)) σ = 1 := by
    intro σ
    rw [← mem_comap_cycZ_princ_two_iff_galChar_eq_one Ω (e + 2) σ]
    change σ ∈ abU Ω (base2 M q d) ∧ _ ↔ _
    simp only [base2, withI, mem_abU_sup_iff, and_assoc]
    rfl
  have hval : ∀ (k : ℕ) [NeZero k], k ∣ N → ∀ σ : G ℚ Ω,
      ((galChar Ω k σ : (ZMod k)ˣ) : ZMod k) = (((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val : ZMod k) :=
    fun k _ hk σ => coe_galChar_eq_val_galChar_of_dvd Ω k N hk σ
  have hone : ∀ (k : ℕ) [NeZero k], k ∣ N → ∀ σ : G ℚ Ω,
      (galChar Ω k σ = 1 ↔ ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val ≡ 1 [MOD k]) := by
    intro k _ hk σ
    rw [Units.ext_iff, hval k hk σ, Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
  have hker : ∀ σ : G ℚ Ω, galChar Ω M.m σ ∈ M.H ↔ M.ker ((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
    intro σ
    constructor
    · intro h
      exact ⟨_, h, hval M.m hMN σ⟩
    · rintro ⟨u, hu, hua⟩
      have : u = galChar Ω M.m σ := Units.ext (by rw [hua, hval M.m hMN σ])
      rwa [← this]
  have hsq : ∀ σ : G ℚ Ω, (galChar Ω (AbF.quad q).m σ ∈ (AbF.quad q).H ↔
      jacobiSym (((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val : ℤ) q = 1) ∧
      (galChar Ω (AbF.quad d).m σ ∈ (AbF.quad d).H ↔
      jacobiSym (((galChar Ω N σ : (ZMod N)ˣ) : ZMod N).val : ℤ) d = 1) := by
    intro σ
    exact ⟨zmod_unit_mem_squares_iff_jacobiSym_eq_one_of_prime q _ hq hqm _ _ (hval _ (by rw [hqm]; exact hqN) σ),
      zmod_unit_mem_squares_iff_jacobiSym_eq_one_of_prime d _ hd hdm _ _ (hval _ (by rw [hdm]; exact hdN) σ)⟩
  have h4 : ∀ σ : G ℚ Ω, galChar Ω (2 ^ (e + 2)) σ = 1 → galChar Ω (AbF.cyc 4).m σ ∈ (AbF.cyc 4).H := by
    intro σ h
    have h4N : (AbF.cyc 4).m ∣ N := by
      rw [h4m]
      exact dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ e + 2)) h2N
    rw [hone _ h2N] at h
    have h1 : galChar Ω (AbF.cyc 4).m σ = 1 := by
      rw [hone _ h4N, h4m]
      exact Nat.ModEq.of_dvd (pow_dvd_pow 2 (by omega : 2 ≤ e + 2)) h
    rw [h1]
    exact Subgroup.one_mem _
  have hle : levU 2 (abU Ω (base2 M q d)) (e + 2) ≤ galOf ℚ E Ω := by
    intro σ hσ
    rw [hlev] at hσ
    obtain ⟨⟨⟨hM, -⟩, hQ, hD⟩, h2⟩ := hσ
    rw [key]
    exact ⟨Or.inl ((hone _ h2N σ).1 h2), (hker σ).1 hM, (hsq σ).1.1 hQ, (hsq σ).2.1 hD⟩
  refine ⟨hle, ?_⟩
  have hsub : (galChar Ω (2 ^ (e + 2))).ker.subgroupOf (galOf ℚ E Ω) ≤
      (levU 2 (abU Ω (base2 M q d)) (e + 2)).subgroupOf (galOf ℚ E Ω) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf, hlev]
    obtain ⟨-, hM, hQ, hD⟩ := (key x).1 x.2
    exact ⟨⟨⟨(hker _).2 hM, h4 _ hx⟩, (hsq _).1.2 hQ, (hsq _).2.2 hD⟩, hx⟩
  refine dvd_trans (Subgroup.index_dvd_of_le hsub) ?_
  rw [Subgroup.subgroupOf, MonoidHom.comap_ker, Subgroup.index_ker]
  have hrange : ((galChar Ω (2 ^ (e + 2))).comp (galOf ℚ E Ω).subtype).range ≤ Subgroup.zpowers (-1) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨h12, -⟩ := (key x).1 x.2
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rcases h12 with h1 | h1
    · rw [(hone _ h2N x).2 h1]
      exact Subgroup.one_mem _
    · have hc := (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
      have hm1 : galChar Ω (2 ^ (e + 2)) x = -1 := by
        ext
        rw [Units.val_neg, Units.val_one, hval _ h2N x, eq_neg_iff_add_eq_zero]
        push_cast at hc
        exact hc
      rw [hm1]
      exact Subgroup.mem_zpowers _
  refine dvd_trans (Subgroup.card_dvd_of_le hrange) ?_
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one (by simp)
