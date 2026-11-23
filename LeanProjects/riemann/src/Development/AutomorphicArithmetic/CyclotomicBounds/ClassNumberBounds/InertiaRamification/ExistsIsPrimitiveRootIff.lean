import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Decomp
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDisc
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDvd

namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

private theorem bv_mem (E : IntermediateField ℚ K) (ψ : DirichletCharacter ℂ N) :
    ψ ∈ fieldChars N E ↔ ∀ σ ∈ E.fixingSubgroup, ψ (galEquivZMod N K σ) = 1 := by
  rw [fieldChars, mem_annihilator_iff]
  constructor
  · intro h σ hσ
    exact h _ ⟨σ, hσ, rfl⟩
  · rintro h _ ⟨σ, hσ, rfl⟩
    exact h σ hσ

private theorem bv_eq [IsAbelianGalois ℚ K] (E : IntermediateField ℚ K) :
    fieldChars N E = intermediateFieldEquivSubgroupChar N K ℂ E := by
  ext ψ
  rw [bv_mem, mem_intermediateFieldEquivSubgroupChar_iff]

private theorem bv_conj (σ : Gal(K/ℚ)) (hσ : galEquivZMod N K σ = -1) (φ : K →+* ℂ)
    (x : K) : φ (σ x) = starRingEnd ℂ (φ x) := by
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have key : φ.toRatAlgHom.comp (σ : K →ₐ[ℚ] K) = ((starRingEnd ℂ).comp φ).toRatAlgHom := by
    apply (hζ.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    change φ (σ _) = starRingEnd ℂ (φ _)
    have h1 : ‖φ (IsCyclotomicExtension.zeta N ℚ K)‖ = 1 :=
      (hζ.map_of_injective φ.injective).norm'_eq_one (NeZero.ne N)
    rw [← Complex.inv_eq_conj h1, ← map_inv₀, galEquivZMod_apply_of_pow_eq N K σ hζ.pow_eq_one, hσ]
    congr 1
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
    simp
  exact DFunLike.congr_fun key x

private theorem bv_real (σ : Gal(K/ℚ)) (hσ : galEquivZMod N K σ = -1) (E : IntermediateField ℚ K)
    (φ : E →+* ℂ) (x : E) : star (φ x) = φ x ↔ σ x = x := by
  have h1 : φ x = ComplexEmbedding.lift K φ (x : K) :=
    (ComplexEmbedding.lift_algebraMap_apply K φ x).symm
  rw [h1, RCLike.star_def, ← bv_conj σ hσ, (ComplexEmbedding.lift K φ).injective.eq_iff]

private theorem bv_complex (E : IntermediateField ℚ K) :
    IsTotallyComplex E ↔ ∃ ψ ∈ fieldChars N E, ψ.Odd := by
  have h := (card_fieldChars (N := N) E).2
  obtain ⟨σ, hσ⟩ := (galEquivZMod N K).surjective (-1)
  constructor
  · intro hc
    by_contra hne
    push Not at hne
    have hr := h.2 fun ψ hψ => ψ.even_or_odd.resolve_right (hne ψ hψ)
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact IsTotallyComplex.complexEmbedding_not_isReal φ (IsTotallyReal.complexEmbedding_isReal φ)
  · rintro ⟨ψ, hψ, hodd⟩
    refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff,
      ComplexEmbedding.isReal_iff]
    intro hw
    refine hodd.not_even ψ (h.1 ⟨fun w' => ?_⟩ ψ hψ)
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    exact (bv_real σ hσ E _ x).2 ((bv_real σ hσ E _ x).1 (RingHom.congr_fun hw x))

theorem fieldChars_lattice :
    Function.Bijective (fun E : IntermediateField ℚ K => fieldChars N E) ∧
      ∀ E E' : IntermediateField ℚ K, (fieldChars N E ≤ fieldChars N E' ↔ E ≤ E') ∧
        fieldChars N (E ⊔ E') = fieldChars N E ⊔ fieldChars N E' ∧
        fieldChars N (E ⊓ E') = fieldChars N E ⊓ fieldChars N E' ∧
        charKer (fieldChars N E) = fieldUnits N E := by
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {N} ℚ K
  refine ⟨?_, fun E E' => ⟨?_, ?_, ?_, (annihilator_charKer ⊥ (fieldUnits N E)).2.1⟩⟩
  · simp only [bv_eq]
    exact (intermediateFieldEquivSubgroupChar N K ℂ).bijective
  · rw [bv_eq, bv_eq, OrderIso.le_iff_le]
  · rw [bv_eq, bv_eq, bv_eq, OrderIso.map_sup]
  · rw [bv_eq, bv_eq, bv_eq, OrderIso.map_inf]

theorem quadratic_discr_iff (E : IntermediateField ℚ K) (d : ℕ) :
    (Module.finrank ℚ E = 2 ∧ discr E = -(d : ℤ)) ↔
      ∃ ψ, IsImagQuad ψ d ∧ fieldChars N E = Subgroup.zpowers ψ := by
  have hcard := (card_fieldChars (N := N) E).1
  have hdisc := (natAbs_discr_eq_finprod_conductor (N := N) E).1
  have hsign := sign_discr E
  have hcx := bv_complex (N := N) E
  have hprod : ∀ ψ ∈ fieldChars N E, ψ.Odd → Nat.card (fieldChars N E) = 2 →
      (discr E).natAbs = ψ.conductor ∧ fieldChars N E = Subgroup.zpowers ψ ∧ ψ ^ 2 = 1 := by
    intro ψ hψ hodd h2
    rw [hdisc]
    generalize fieldChars N E = X at hψ h2
    have hne : (⟨ψ, hψ⟩ : X) ≠ 1 := by
      intro h
      have h' : ψ = 1 := congrArg Subtype.val h
      apply hodd.not_even ψ
      rw [h', DirichletCharacter.Even]
      exact MulChar.one_apply (isUnit_one.neg)
    have hall : ∀ χ : X, χ = 1 ∨ χ = ⟨ψ, hψ⟩ := by
      intro χ
      have h3 := (Nat.card_eq_two_iff' (1 : X)).1 h2
      by_cases h1 : χ = 1
      · exact Or.inl h1
      · exact Or.inr (h3.unique h1 hne)
    refine ⟨?_, ?_, ?_⟩
    · rw [finprod_eq_single _ (⟨ψ, hψ⟩ : X)]
      intro χ hχ
      rw [(hall χ).resolve_right hχ]
      exact conductor_one
    · refine le_antisymm (fun χ hχ => ?_) (by simpa using hψ)
      rcases hall ⟨χ, hχ⟩ with h | h
      · rw [show χ = 1 from congrArg Subtype.val h]
        exact one_mem _
      · rw [show χ = ψ from congrArg Subtype.val h]
        exact Subgroup.mem_zpowers _
    · have h4 : (⟨ψ, hψ⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
      rw [h2] at h4
      exact congrArg Subtype.val h4
  have hrk := InfinitePlace.card_add_two_mul_card_eq_rank E
  constructor
  · rintro ⟨h2, hd⟩
    have hneg : discr E < 0 := lt_of_le_of_ne (by omega) (discr_ne_zero E)
    rw [Int.sign_eq_neg_one_of_neg hneg] at hsign
    have h0 : InfinitePlace.nrComplexPlaces E ≠ 0 := by
      intro h
      rw [h] at hsign
      simp at hsign
    obtain ⟨ψ, hψ, hodd⟩ := hcx.1 (nrRealPlaces_eq_zero_iff.1 (by omega))
    obtain ⟨a, b, c⟩ := hprod ψ hψ hodd (hcard.trans h2)
    exact ⟨ψ, ⟨c, hodd, by omega⟩, b⟩
  · rintro ⟨ψ, ⟨h1, hodd, hc⟩, hX⟩
    have hψ : ψ ∈ fieldChars N E := hX ▸ Subgroup.mem_zpowers ψ
    have hne : ψ ≠ 1 := by
      intro h'
      apply hodd.not_even ψ
      rw [h', DirichletCharacter.Even]
      exact MulChar.one_apply (isUnit_one.neg)
    have h2 : Nat.card (fieldChars N E) = 2 := by
      rw [hX, Nat.card_zpowers, orderOf_eq_prime h1 hne]
    have h0 := nrRealPlaces_eq_zero_iff.2 (hcx.2 ⟨ψ, hψ, hodd⟩)
    have h3 : InfinitePlace.nrComplexPlaces E = 1 := by omega
    rw [h3, pow_one, Int.sign_eq_neg_one_iff_neg] at hsign
    have := (hprod ψ hψ hodd h2).1
    exact ⟨by omega, by omega⟩

end KStar.Ram
