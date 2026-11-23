import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UMFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem res_entry {R : Type} [CommRing R] [IsLocalRing R] {X X' : M4 R} (hX : Sep X) (h : X' * X = 1) (Y : M4 R)
    (i j : Fin 4) : residue R (X' j j) * residue R (X j j) = 1 ∧
      residue R ((X * Y * X' - Y) i j) = residue R ((X i i - X j j) * X' j j) * residue R (Y i j) := by
  have hoff : ∀ a b, a ≠ b → residue R (X a b) = 0 :=
    fun a b hab => (residue_eq_zero_iff _).2 (hX.off a b hab)
  have kr : ∀ (A B : M4 R), (∀ a b, a ≠ b → residue R (B a b) = 0) →
      ∀ a b, residue R ((A * B) a b) = residue R (A a b) * residue R (B b b) := by
    intro A B hB a b
    rw [Matrix.mul_apply, map_sum, Finset.sum_eq_single b]
    · rw [map_mul]
    · intro c _ hc
      rw [map_mul, hB c b hc, mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  have kl : ∀ (A B : M4 R), (∀ a b, a ≠ b → residue R (A a b) = 0) →
      ∀ a b, residue R ((A * B) a b) = residue R (A a a) * residue R (B a b) := by
    intro A B hA a b
    rw [Matrix.mul_apply, map_sum, Finset.sum_eq_single a]
    · rw [map_mul]
    · intro c _ hc
      rw [map_mul, hA a c (Ne.symm hc), zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  have hdiag : ∀ j, residue R (X' j j) * residue R (X j j) = 1 := by
    intro j
    rw [← kr X' X hoff j j, h, Matrix.one_apply_eq, map_one]
  have hoff' : ∀ a b, a ≠ b → residue R (X' a b) = 0 := by
    intro a b hab
    have h0 : residue R (X' a b) * residue R (X b b) = 0 := by
      rw [← kr X' X hoff a b, h, Matrix.one_apply_ne hab, map_zero]
    linear_combination residue R (X' b b) * h0 - residue R (X' a b) * hdiag b
  refine ⟨hdiag j, ?_⟩
  rw [Matrix.sub_apply, map_sub, kr _ _ hoff' i j, kl _ _ hoff i j, map_mul, map_sub]
  linear_combination residue R (Y i j) * hdiag j

theorem UpperTheory.V.Ws.Bl.adBij :
    ∀ (R Γ : Type) [CommRing R] [IsLocalRing R] [Group Γ] (r : Γ →* M4 R) (h : BG r) (s : Γ), Sep (r s) → Function.Bijective fun Y => adU h s Y - Y := by
  intro R Γ _ _ _ r h s hs
  obtain ⟨hfin, -, hmem⟩ := uMFacts R
  haveI := hfin
  let φ : uM R →ₗ[R] uM R := adU h s - LinearMap.id
  have hinv : r s⁻¹ * r s = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hkey : ∀ Y : uM R, φ Y ∈ (maximalIdeal R • ⊤ : Submodule R (uM R)) →
      Y ∈ (maximalIdeal R • ⊤ : Submodule R (uM R)) := by
    intro Y hY
    rw [hmem] at hY ⊢
    intro i j
    by_cases hij : lamW i < lamW j
    · have h1 := hY i j
      have e := res_entry hs hinv (Y : M4 R) i j
      have hu : IsUnit (r s i i - r s j j) := hs.unit i j (ne_of_lt hij)
      have hc : (↑(φ Y) : M4 R) i j = (r s * ↑Y * r s⁻¹ - ↑Y) i j := rfl
      rw [hc, ← residue_eq_zero_iff, e.2, map_mul] at h1
      rw [← residue_eq_zero_iff]
      have hu' : residue R (r s i i - r s j j) ≠ 0 := (hu.map (residue R)).ne_zero
      have hv : residue R (r s⁻¹ j j) ≠ 0 := left_ne_zero_of_mul_eq_one e.1
      exact (mul_eq_zero.1 h1).resolve_left (mul_ne_zero hu' hv)
    · have hY2 := (Submodule.mem_inf.1 Y.2).1
      rw [hY2 i j hij]
      exact zero_mem _
  have hS : (maximalIdeal R • ⊤ : Submodule R (uM R)) ≤
      (maximalIdeal R • ⊤ : Submodule R (uM R)).comap φ := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  let ψ := Submodule.mapQ _ _ φ hS
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨Y, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hkey Y hq
  letI : Module (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    inferInstanceAs (Module (R ⧸ maximalIdeal R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))))
  letI : IsScalarTower R (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    inferInstanceAs (IsScalarTower R (R ⧸ maximalIdeal R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))))
  haveI : Module.Finite (ResidueField R) (uM R ⧸ (maximalIdeal R • ⊤ : Submodule R (uM R))) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hsurjA : Function.Surjective (algebraMap R (ResidueField R)) := Ideal.Quotient.mk_surjective
  let ψk := LinearMap.extendScalarsOfSurjective hsurjA ψ
  have hψsurj : Function.Surjective ψ := (LinearMap.injective_iff_surjective (f := ψk)).1 hψinj
  have hrange : LinearMap.range φ = ⊤ := by
    rw [← IsLocalRing.map_mkQ_eq_top, ← LinearMap.range_comp, eq_top_iff]
    intro q _
    obtain ⟨q', rfl⟩ := hψsurj q
    obtain ⟨Y, rfl⟩ := Submodule.mkQ_surjective _ q'
    exact ⟨Y, rfl⟩
  have hsurj : Function.Surjective φ := LinearMap.range_eq_top.1 hrange
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism φ hsurj, hsurj⟩
