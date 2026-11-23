import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

private theorem act_root {K : Type} [Field K] {N : ℕ} [NeZero N] {ζ x : K} (hζ : IsPrimitiveRoot ζ N)
    (σ : K →+* K) {a : ℕ} (hσ : σ ζ = ζ ^ a) (hx : x ^ N = 1) : σ x = x ^ a := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
  rw [map_pow, hσ, pow_right_comm]

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

private theorem exists_res {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] [Normal ℚ K]
    (f : K →ₐ[ℚ] L) (σ : L ≃ₐ[ℚ] L) : ∃ τ : K ≃ₐ[ℚ] K, ∀ x : K, σ (f x) = f (τ x) := by
  letI : Algebra K L := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact ⟨σ.restrictNormal K, fun x => (σ.restrictNormal_commutes K x).symm⟩

private theorem equiv_of_range {F L L' Ω : Type} [Field F] [Field L] [Field L'] [Field Ω] [Algebra F L]
    [Algebra F L'] [Algebra F Ω] (g : L →ₐ[F] Ω) (g' : L' →ₐ[F] Ω) (e : g.fieldRange = g'.fieldRange) :
    Nonempty (L ≃+* L') :=
  ⟨((g.equivFieldRange.trans (IntermediateField.equivOfEq e)).trans g'.equivFieldRange.symm).toRingEquiv⟩

private theorem equiv_of_fix {L L' Ω : Type} [Field L] [Field L'] [Field Ω] [Algebra ℚ L] [Algebra ℚ L']
    [Algebra ℚ Ω] [IsGalois ℚ Ω] (g : L →ₐ[ℚ] Ω) (g' : L' →ₐ[ℚ] Ω)
    (h : ∀ σ : Ω ≃ₐ[ℚ] Ω, (∀ x, σ (g x) = g x) ↔ ∀ x, σ (g' x) = g' x) : Nonempty (L ≃+* L') := by
  have e : g.fieldRange = g'.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup g.fieldRange,
      ← InfiniteGalois.fixedField_fixingSubgroup g'.fieldRange]
    congr 1
    ext σ
    rw [mem_fix, mem_fix, h]
  exact equiv_of_range g g' e

theorem UpperTheory.V.Win.abiso :
    ∀ (A : AbF) (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'],
      IsAbField A L → IsAbField A L' → Nonempty (L ≃+* L') := by
  intro A L L' _ _ _ _ hL hL'
  obtain ⟨N, hN, i, ζ, hm, hζ, H0⟩ := hL
  obtain ⟨N', hN', j, ζ', hm', hζ', H⟩ := hL'
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsCyclotomicExtension {N'} ℚ (CyclotomicField N' ℚ) := CyclotomicField.isCyclotomicExtension _ ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isAbelianGalois {N} ℚ _
  haveI : IsAbelianGalois ℚ (CyclotomicField N' ℚ) := IsCyclotomicExtension.isAbelianGalois {N'} ℚ _
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := by
    first
      | exact @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
      | convert @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
  let f : CyclotomicField N ℚ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let f' : CyclotomicField N' ℚ →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  refine equiv_of_fix (f.comp i) (f'.comp j) fun σ => ?_
  obtain ⟨τ, hσ⟩ := exists_res f σ
  obtain ⟨τ', hσ'⟩ := exists_res f' σ
  obtain ⟨a, hτ⟩ := exists_pow hζ τ
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
  have h4 : A.ker a ↔ A.ker b := ⟨ker_congr A hab.symm, ker_congr A hab⟩
  have e1 : (∀ x, σ ((f.comp i) x) = (f.comp i) x) ↔ ∀ x, τ (i x) = i x := by
    refine forall_congr' fun x => ?_
    show σ (f (i x)) = f (i x) ↔ _
    rw [hσ]
    exact f.injective.eq_iff
  have e2 : (∀ x, σ ((f'.comp j) x) = (f'.comp j) x) ↔ ∀ x, τ' (j x) = j x := by
    refine forall_congr' fun x => ?_
    show σ (f' (j x)) = f' (j x) ↔ _
    rw [hσ']
    exact f'.injective.eq_iff
  rw [e1, e2, H0 τ a hτ, H τ' b hb, h4]
