import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar
import Development.AutomorphicArithmetic.QuadraticCharacters.GaussRoot

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

private theorem act_root {K : Type} [Field K] {N : ℕ} [NeZero N] {ζ x : K} (hζ : IsPrimitiveRoot ζ N)
    (σ : K →+* K) {a : ℕ} (hσ : σ ζ = ζ ^ a) (hx : x ^ N = 1) : σ x = x ^ a := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hσ, pow_right_comm]

private theorem coprime_of {K : Type} [Field K] {N : ℕ} [NeZero N] {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (σ : K →+* K) {a : ℕ} (hσ : σ ζ = ζ ^ a) : a.Coprime N := by
  have h1 : IsPrimitiveRoot (ζ ^ a) N := by
    rw [← hσ]
    exact hζ.map_of_injective σ.injective
  exact (hζ.pow_iff_coprime (NeZero.pos N) a).1 h1

private theorem sqrt_iff {K : Type} [Field K] [CharZero K] {N : ℕ} [NeZero N] {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    (σ : K →+* K) {a : ℕ} (hσ : σ ζ = ζ ^ a) {q : ℕ} (hq : q.Prime) (h4 : q % 4 = 3) (hd : q ∣ N)
    {α : K} (hα : α ^ 2 = -(q : K)) : σ α = α ↔ jacobiSym (a : ℤ) q = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk⟩ := hd
  have hω : IsPrimitiveRoot (ζ ^ k) q := hζ.pow (NeZero.pos N) (by rw [hk, mul_comm])
  obtain ⟨G, hG, hs⟩ := HostParam.SlopeTestRemainingChoices.GaussRoot.exists_gauss h4 hω
  have hc : a.Coprime q := (coprime_of hζ σ hσ).coprime_dvd_right ⟨k, hk⟩
  have h1 := hs σ a hc (by rw [map_pow, hσ, pow_right_comm])
  have h2 : σ α = ((quadraticChar (ZMod q) (a : ZMod q) : ℤ) : K) * α := by
    rcases HostParam.SlopeTestRemainingChoices.GaussRoot.eq_or_neg hα hG with rfl | rfl
    · exact h1
    · rw [map_neg, h1, mul_neg]
  have h3 : jacobiSym (a : ℤ) q = quadraticChar (ZMod q) (a : ZMod q) := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast]
  rw [h3, h2, mul_left_eq_self₀, or_iff_left (HostParam.SlopeTestRemainingChoices.GaussRoot.ne_zero hq hα), Int.cast_eq_one]

private theorem trace_iff {K : Type} [Field K] {n : ℕ} (hn : n ≠ 0) {η : K} (hη : IsPrimitiveRoot η n) (a : ℕ) :
    η ^ a + (η ^ a)⁻¹ = η + η⁻¹ ↔ (a ≡ 1 [MOD n] ∨ a + 1 ≡ 0 [MOD n]) := by
  have h0 : η ≠ 0 := hη.ne_zero hn
  have h1 : η ^ a ≠ 0 := pow_ne_zero _ h0
  have hfin : IsOfFinOrder η := hη.isOfFinOrder hn
  have e1 : a ≡ 1 [MOD n] ↔ η ^ a = η := by
    rw [hη.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_one]
  have e2 : a + 1 ≡ 0 [MOD n] ↔ η ^ a * η = 1 := by
    rw [hη.eq_orderOf, ← hfin.pow_eq_pow_iff_modEq, pow_zero, pow_succ]
  rw [e1, e2]
  generalize η ^ a = y at h1
  have key : y + y⁻¹ - (η + η⁻¹) = (y - η) * (y * η - 1) / (y * η) := by
    field_simp
    ring
  rw [← sub_eq_zero, key, div_eq_zero_iff, or_iff_left (mul_ne_zero h1 h0), mul_eq_zero, sub_eq_zero,
    sub_eq_zero]

private theorem exists_pow {N : ℕ} [NeZero N] {ζ : CyclotomicField N ℚ} (hζ : IsPrimitiveRoot ζ N)
    (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) : ∃ a : ℕ, τ ζ = ζ ^ a := by
  obtain ⟨i, -, h⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  exact ⟨i, h.symm⟩

private theorem mem_fix {E K : Type} [Field E] [Field K] [Algebra ℚ E] [Algebra ℚ K] (j : E →ₐ[ℚ] K)
    (τ : K ≃ₐ[ℚ] K) : τ ∈ j.fieldRange.fixingSubgroup ↔ ∀ x : E, τ (j x) = j x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x => h _ ⟨x, rfl⟩, fun h _ ⟨x, hx⟩ => hx ▸ h x⟩

private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) (hb : A.ker b) : A.ker a := by
  obtain ⟨u, hu, e⟩ := hb
  exact ⟨u, hu, e.trans ((ZMod.natCast_eq_natCast_iff _ _ _).2 h).symm⟩

private theorem range_le {M L : Type} [Field M] [Field L] [Algebra ℚ M] [Algebra ℚ L] [Normal ℚ M]
    (g₁ g₂ : M →ₐ[ℚ] L) (x : M) : ∃ y : M, g₂ y = g₁ x := by
  letI : Algebra M L := g₂.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ M L := IsScalarTower.of_algebraMap_eq fun r => (g₂.commutes r).symm
  exact ⟨g₁.restrictNormal M x, g₁.restrictNormal_commutes M x⟩

private theorem exists_lift {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] [Normal ℚ L]
    (f : K →ₐ[ℚ] L) (τ : K ≃ₐ[ℚ] K) : ∃ σ : L ≃ₐ[ℚ] L, ∀ x : K, σ (f x) = f (τ x) := by
  letI : Algebra K L := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact ⟨τ.liftNormal L, fun x => τ.liftNormal_commutes L x⟩

private theorem exists_res {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] [Normal ℚ K]
    (f : K →ₐ[ℚ] L) (σ : L ≃ₐ[ℚ] L) : ∃ τ : K ≃ₐ[ℚ] K, ∀ x : K, σ (f x) = f (τ x) := by
  letI : Algebra K L := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact ⟨σ.restrictNormal K, fun x => (σ.restrictNormal_commutes K x).symm⟩

private theorem indep (A : AbF) {M : Type} [Field M] [NumberField M] (hM : IsAbField A M) {N : ℕ} [NeZero N]
    (hm : A.m ∣ N) (i : M →ₐ[ℚ] CyclotomicField N ℚ) {ζ : CyclotomicField N ℚ} (hζ : IsPrimitiveRoot ζ N)
    (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ) (hτ : τ ζ = ζ ^ a) :
    (∀ x : M, τ (i x) = i x) ↔ A.ker a := by
  obtain ⟨N', hN', j, ζ', hm', hζ', H⟩ := hM
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsCyclotomicExtension {N'} ℚ (CyclotomicField N' ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isAbelianGalois {N} ℚ _
  haveI : IsAbelianGalois ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.isAbelianGalois {N'} ℚ _
  haveI : IsAbelianGalois ℚ M := IsAbelianGalois.of_algHom j
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    first
      | exact @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _
      | convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _
  let f : CyclotomicField N ℚ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let f' : CyclotomicField N' ℚ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  obtain ⟨σ, hσ⟩ := exists_lift f τ
  obtain ⟨τ', hσ'⟩ := exists_res f' σ
  obtain ⟨b, hb⟩ := exists_pow hζ' τ'
  obtain ⟨k, hk⟩ := id hm
  obtain ⟨k', hk'⟩ := id hm'
  have hω : IsPrimitiveRoot (f (ζ ^ k)) A.m :=
    (hζ.pow (NeZero.pos N) (by rw [hk, mul_comm])).map_of_injective f.injective
  have hω' : IsPrimitiveRoot (f' (ζ' ^ k')) A.m :=
    (hζ'.pow (NeZero.pos N') (by rw [hk', mul_comm])).map_of_injective f'.injective
  have h1 : σ (f (ζ ^ k)) = f (ζ ^ k) ^ a := by
    rw [hσ, map_pow τ, hτ, pow_right_comm, map_pow f]
  have h2 : σ (f' (ζ' ^ k')) = f' (ζ' ^ k') ^ b := by
    rw [hσ', map_pow τ', hb, pow_right_comm, map_pow f']
  have h3 : σ (f (ζ ^ k)) = f (ζ ^ k) ^ b :=
    act_root hω' (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) h2 hω.pow_eq_one
  have hab : a ≡ b [MOD A.m] := by
    have := ((hω.isOfFinOrder A.pos.ne').pow_eq_pow_iff_modEq).1 (h1.symm.trans h3)
    rwa [← hω.eq_orderOf] at this
  have h4 : A.ker b ↔ A.ker a := ⟨ker_congr A hab, ker_congr A hab.symm⟩
  rw [← h4, ← H τ' b hb]
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := range_le (f'.comp j) (f.comp i) x
    have hy' : f (i y) = f' (j x) := hy
    apply f'.injective
    show f' (τ' (j x)) = f' (j x)
    rw [← hσ', ← hy', hσ, h]
  · intro h x
    obtain ⟨y, hy⟩ := range_le (f.comp i) (f'.comp j) x
    have hy' : f' (j y) = f (i x) := hy
    apply f.injective
    show f (τ (i x)) = f (i x)
    rw [← hσ, ← hy', hσ', h]

private theorem core (A : AbF) {M : Type} [Field M] [NumberField M] (hM : IsAbField A M)
    {e q d : ℕ} (hq : q.Prime) (hd : d.Prime) (hq4 : q % 4 = 3) (hd4 : d % 4 = 3)
    {N : ℕ} [NeZero N] (i : M →ₐ[ℚ] CyclotomicField N ℚ)
    {ζ η α β : CyclotomicField N ℚ} (h2 : 2 ^ (e + 2) ∣ N) (hm : A.m ∣ N) (hqN : q ∣ N)
    (hdN : d ∣ N) (hζ : IsPrimitiveRoot ζ N) (hη : IsPrimitiveRoot η (2 ^ (e + 2)))
    (hα : α ^ 2 = -(q : CyclotomicField N ℚ)) (hβ : β ^ 2 = -(d : CyclotomicField N ℚ))
    (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ) (hτ : τ ζ = ζ ^ a) :
    τ ∈ (IntermediateField.adjoin ℚ {α, β, η + η⁻¹} ⊔ i.fieldRange).fixingSubgroup ↔
      (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧
          jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1 := by
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  have hτ' : (τ : CyclotomicField N ℚ →+* CyclotomicField N ℚ) ζ = ζ ^ a := hτ
  have e1 : τ α = α ↔ jacobiSym (a : ℤ) q = 1 := sqrt_iff hζ _ hτ' hq hq4 hqN hα
  have e2 : τ β = β ↔ jacobiSym (a : ℤ) d = 1 := sqrt_iff hζ _ hτ' hd hd4 hdN hβ
  have hηa : τ η = η ^ a := act_root hζ _ hτ' ((hη.pow_eq_one_iff_dvd N).2 h2)
  have e3 : τ (η + η⁻¹) = η + η⁻¹ ↔ (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) := by
    rw [map_add, map_inv₀, hηa]
    exact trace_iff (pow_ne_zero _ two_ne_zero) hη a
  have e4 : τ ∈ (IntermediateField.adjoin ℚ {α, β, η + η⁻¹}).fixingSubgroup ↔
      τ α = α ∧ τ β = β ∧ τ (η + η⁻¹) = η + η⁻¹ := by
    rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
    have hm : ∀ x : CyclotomicField N ℚ, x ∈ IntermediateField.fixedField (Subgroup.zpowers τ) ↔ τ x = x := by
      intro x
      rw [IntermediateField.mem_fixedField_iff]
      refine ⟨fun h => h τ (Subgroup.mem_zpowers τ), fun h f hf => ?_⟩
      have : Subgroup.zpowers τ ≤ MulAction.stabilizer _ x := Subgroup.zpowers_le.2 h
      exact this hf
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe, hm]
  rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf, mem_fix,
    e4, e1, e2, e3, indep A hM hm i hζ τ a hτ]
  tauto
