import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRedRes

theorem residue_perfect_and_char :
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [PerfectField (ResidueField R)] (L W : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra W L] [IsFractionRing W L], IsAbove R K (algebraMap W L).range → PerfectField (ResidueField W) ∧ ∀ m : ℕ, (m : ResidueField R) ≠ 0 → (m : ResidueField W) ≠ 0 := by
  intro R K _ _ _ _ _ _ _ L W _ _ _ _ _ _ _ _ h
  have hWL : Function.Injective (algebraMap W L) := IsFractionRing.injective W L
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  set V : Subring L := (algebraMap W L).range with hV
  have memV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ (algebraMap R K).range := by
    intro x
    rw [← Subring.mem_comap, show V.comap (algebraMap K L) = (algebraMap R K).range from h]
  let e : W ≃+* V := RingEquiv.ofBijective (algebraMap W L).rangeRestrict
    ⟨fun a b hab => hWL (by simpa using congrArg Subtype.val hab), (algebraMap W L).rangeRestrict_surjective⟩
  have he : ∀ v : V, algebraMap W L (e.symm v) = v := by
    intro v
    have := congrArg Subtype.val (e.apply_symm_apply v)
    exact this
  let ψ : R →+* V := ((algebraMap K L).comp (algebraMap R K)).codRestrict V
    (fun r => (memV _).2 ⟨r, rfl⟩)
  let φ : R →+* W := e.symm.toRingHom.comp ψ
  have hφ : ∀ r, algebraMap W L (φ r) = algebraMap K L (algebraMap R K r) := by
    intro r; exact he (ψ r)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have := congrArg (algebraMap W L) hab
    rw [hφ, hφ] at this
    exact hRK ((algebraMap K L).injective this)
  haveI : IsLocalHom φ := by
    constructor
    intro r hr
    obtain ⟨u, hu⟩ := hr
    have hx : algebraMap W L (φ r) * algebraMap W L (u⁻¹ : Wˣ) = 1 := by
      rw [← map_mul, ← hu]; simp
    rw [hφ] at hx
    have hx0 : algebraMap R K r ≠ 0 := by
      intro h0; rw [h0] at hx; simp at hx
    have hinv : algebraMap K L (algebraMap R K r)⁻¹ = algebraMap W L (u⁻¹ : Wˣ) := by
      rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_right hx).symm
    obtain ⟨s, hs⟩ := (memV _).1 (by rw [hinv]; exact RingHom.mem_range_self _ _)
    have h1 : r * s = 1 := hRK (by rw [map_mul, hs, map_one, mul_inv_cancel₀ hx0])
    exact ⟨⟨r, s, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  let f := ResidueField.map φ
  have hf : Function.Injective f := f.injective
  refine ⟨?_, fun m hm hW => hm (hf (by rw [map_natCast, map_zero]; exact hW))⟩
  letI : Algebra (ResidueField R) (ResidueField W) := f.toAlgebra
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := R)
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField W) := by
    constructor
    intro y
    obtain ⟨w, rfl⟩ := residue_surjective y
    have hint : IsIntegral K (algebraMap W L w) := Algebra.IsIntegral.isIntegral _
    set p := minpoly K (algebraMap W L w)
    obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors R) p
    set q := IsLocalization.integerNormalization (nonZeroDivisors R) p
    have hp0 : p ≠ 0 := minpoly.ne_zero hint
    have hq0 : q ≠ 0 := by
      intro hq; rw [hq, Polynomial.map_zero] at hb
      have hb0 : (algebraMap R K (b : R)) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
      rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hb
      exact hp0 ((mul_eq_zero.1 hb.symm).resolve_left (by simpa using hb0))
    have hqw : Polynomial.eval₂ φ w q = 0 := by
      apply hWL
      rw [map_zero, Polynomial.hom_eval₂]
      have : (algebraMap W L).comp φ = (algebraMap K L).comp (algebraMap R K) := RingHom.ext hφ
      rw [this, ← Polynomial.eval₂_map, hb]
      rw [Algebra.smul_def, Polynomial.eval₂_mul]
      have : Polynomial.eval₂ (algebraMap K L) (algebraMap W L w) p = 0 := minpoly.aeval K _
      rw [this, mul_zero]
    set pp := q.primPart
    have hpp : Polynomial.eval₂ φ w pp = 0 := by
      have hc : q.content ≠ 0 := (Polynomial.content_eq_zero_iff).not.2 hq0
      have := hqw
      rw [Polynomial.eq_C_content_mul_primPart q, Polynomial.eval₂_mul, Polynomial.eval₂_C] at this
      exact (mul_eq_zero.1 this).resolve_left (fun h0 => hc (hφinj (by rw [h0, map_zero])))
    refine ⟨pp.map (residue R), ?_, ?_⟩
    · intro h0
      have hmem : pp ∈ RingHom.ker (Polynomial.mapRingHom (residue R)) := by
        simpa [RingHom.mem_ker] using h0
      rw [Polynomial.ker_mapRingHom, ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
        Set.image_singleton, Ideal.mem_span_singleton] at hmem
      exact hϖ.not_isUnit (Polynomial.isPrimitive_primPart q ϖ hmem)
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      change Polynomial.eval₂ (f.comp (residue R)) _ _ = 0
      rw [ResidueField.map_comp_residue, ← Polynomial.hom_eval₂, hpp, map_zero]
  exact Algebra.IsAlgebraic.perfectField (ResidueField R)

end GlobalTheory.AbVarRedRes
