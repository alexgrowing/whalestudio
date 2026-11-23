import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem isCM_of_conj (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) : IsCMField K := by
  classical
  choose c hc using h
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hcc : ∀ x, c (c x) = x := fun x => φ.injective (by rw [hc, hc, Complex.conj_conj])
  let τ : K ≃+* K :=
    { toFun := c
      invFun := c
      left_inv := hcc
      right_inv := hcc
      map_mul' := fun x y => φ.injective (by simp only [hc, map_mul])
      map_add' := fun x y => φ.injective (by simp only [hc, map_add]) }
  let σ : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)
  have hσ : ∀ ψ : K →+* ℂ, ComplexEmbedding.IsConj ψ σ := fun ψ => by
    ext x
    exact (hc x ψ).symm
  have hσ' : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers, ComplexEmbedding.orderOf_isConj_two_of_ne_one (hσ φ)]
    exact (ComplexEmbedding.isConj_ne_one_iff (hσ φ)).mpr <| IsTotallyComplex.complexEmbedding_not_isReal φ
  let L := (FixedPoints.intermediateField (Subgroup.zpowers σ) : IntermediateField ℚ K)
  have : IsTotallyReal L := ⟨fun w ↦ by
    obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
    dsimp only
    rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff]
    ext x
    have hx : c x.1 = x.1 := x.2 ⟨σ, Subgroup.mem_zpowers σ⟩
    have := hc x.1 W.embedding
    rw [hx] at this
    exact this.symm⟩
  have : Algebra.IsQuadraticExtension L K := ⟨by
    have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
    rw [← hσ', Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K⟩
  exact IsCMField.ofCMExtension L K

theorem UpperTheory.V.Kum.fnCM :
    ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), IsCMField (Fn F Ω l n) := by
  intro F Ω _ _ _ _ _ _ l _ n
  have : IsTotallyComplex (Fn F Ω l n) := isTotallyComplex_of_algebra F (Fn F Ω l n)
  refine isCM_of_conj _ ?_
  rintro ⟨x, hx⟩
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    have hx1 : x ^ l ^ n = 1 := by
      have := Polynomial.aeval_eq_zero_of_mem_rootSet hx
      simpa [sub_eq_zero] using this
    let z : Fn F Ω l n := ⟨x, IntermediateField.subset_adjoin F _ hx⟩
    have hz : z ^ l ^ n = 1 := Subtype.ext hx1
    refine ⟨z⁻¹, fun φ => ?_⟩
    have : ‖φ z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hz, map_one]) hN0
    rw [map_inv₀, Complex.inv_eq_conj this]
  | algebraMap a =>
    exact ⟨algebraMap F _ (IsCMField.complexConj F a), fun φ =>
      IsCMField.complexEmbedding_complexConj F (φ.comp (algebraMap F (Fn F Ω l n))) a⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    refine ⟨a + b, fun φ => ?_⟩
    rw [map_add, ha, hb, ← map_add, ← map_add]
    rfl
  | inv x hx ihx =>
    obtain ⟨a, ha⟩ := ihx
    refine ⟨a⁻¹, fun φ => ?_⟩
    rw [map_inv₀, ha, ← map_inv₀, ← map_inv₀]
    rfl
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    refine ⟨a * b, fun φ => ?_⟩
    rw [map_mul, ha, hb, ← map_mul, ← map_mul]
    rfl
