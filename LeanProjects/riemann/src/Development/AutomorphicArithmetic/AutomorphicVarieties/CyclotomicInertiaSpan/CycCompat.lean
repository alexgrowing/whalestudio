import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.OnePrimeOfTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.B1

private theorem exists_primitiveRoot_algClosure_numberField (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (M : ℕ) [NeZero M] : ∃ ζ : Ω, IsPrimitiveRoot ζ M := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω M

private theorem cycN_apply_primitiveRoot_eq_pow (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (N : ℕ) [NeZero N] (g : G F Ω) {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) :
    g ζ = ζ ^ ((cycN F Ω N g : (ZMod N)ˣ) : ZMod N).val := by
  have hu := (hζ.isUnit_unit NeZero.out).mem_rootsOfUnity
  have := modularCyclotomicCharacter.spec Ω (natCard_roots F Ω N)
    (MulSemiringAction.toRingAut (G F Ω) Ω g) hu
  simpa [cycN] using this

private theorem zmod_eq_intCast_of_primitiveRoot_pow_eq {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) (k : ℤ) (h : ζ ^ a.val = ζ ^ k) :
    a = (k : ZMod N) := by
  have h0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  have h1 : ζ ^ ((a.val : ℤ) - k) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, h, div_self (zpow_ne_zero _ h0)]
  have h2 := (hζ.zpow_eq_one_iff_dvd _).mp h1
  have h3 : (((a.val : ℤ) - k : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h2
  push_cast at h3
  rw [ZMod.natCast_zmod_val] at h3
  exact sub_eq_zero.mp h3

theorem UpperTheory.V.B1.cycCompat :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) [NeZero N], IsOpen ((cycN F Ω N).ker : Set (G F Ω)) ∧
    (∀ (M : ℕ) [NeZero M] (h : M ∣ N) (g : G F Ω), ZMod.unitsMap h (cycN F Ω N g) = cycN F Ω M g) ∧
    ∀ c : G F Ω, IsConjOm c.toRingEquiv → cycN F Ω N c = -1 := by
  intro F Ω _ _ _ _ _ N _
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_algClosure_numberField F Ω N
  refine ⟨?_, ?_, ?_⟩
  · haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin F {ζ}).fixingSubgroup) ?_
      (IntermediateField.fixingSubgroup_isOpen _)
    intro g hg
    have hgz : g ζ = ζ := by
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ
        (IntermediateField.mem_adjoin_simple_self F ζ)
      simpa [AlgEquiv.smul_def] using this
    rw [MonoidHom.mem_ker]
    apply Units.ext
    have := zmod_eq_intCast_of_primitiveRoot_pow_eq hζ _ 1 (by rw [← cycN_apply_primitiveRoot_eq_pow F Ω N g hζ, hgz, zpow_one])
    simpa using this
  · intro M _ h g
    obtain ⟨d, hd⟩ := id h
    have hη := hζ.pow (NeZero.pos N) (show N = d * M by rw [hd, mul_comm])
    have e1 : g (ζ ^ d) = (ζ ^ d) ^ ((cycN F Ω N g : (ZMod N)ˣ) : ZMod N).val := by
      rw [map_pow, cycN_apply_primitiveRoot_eq_pow F Ω N g hζ, ← pow_mul, ← pow_mul, mul_comm]
    have e2 := cycN_apply_primitiveRoot_eq_pow F Ω M g hη
    have key := zmod_eq_intCast_of_primitiveRoot_pow_eq hη _ (((cycN F Ω N g : (ZMod N)ˣ) : ZMod N).val : ℤ)
      (by rw [← e2, e1, zpow_natCast])
    apply Units.ext
    rw [key, Int.cast_natCast, ← ZMod.cast_eq_val, ZMod.unitsMap_def]
    rfl
  · intro c hc
    obtain ⟨j, hj⟩ := hc
    apply Units.ext
    have hN : ζ ^ N = 1 := hζ.pow_eq_one
    have hcz : c ζ = ζ⁻¹ := by
      apply j.injective
      have := hj ζ
      simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv] at this
      rw [this, map_inv₀]
      have hn : ‖j ζ‖ = 1 :=
        Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hN, map_one]) (NeZero.ne N)
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
      simp
    have := zmod_eq_intCast_of_primitiveRoot_pow_eq hζ _ (-1) (by rw [← cycN_apply_primitiveRoot_eq_pow F Ω N c hζ, hcz, zpow_neg_one])
    simpa using this
