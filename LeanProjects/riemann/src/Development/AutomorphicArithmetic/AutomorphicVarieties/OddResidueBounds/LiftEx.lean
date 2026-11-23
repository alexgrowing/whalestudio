import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.liftEx :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N], (∀ b : (ZMod N)ˣ, ∃ σ : Ω ≃+* Ω, CycLift N b σ) ∧ ∀ σ : Ω ≃+* Ω, ∃ b : (ZMod N)ˣ, CycLift N b σ := by
  intro E Ω _ _ _ _ _ N _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have hN : NeZero (N : Ω) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hpos : 0 < N := NeZero.pos N
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N Ω) (Polynomial.degree_cyclotomic_pos N Ω hpos).ne'
  have hζp : IsPrimitiveRoot ζ N := Polynomial.isRoot_cyclotomic_iff.mp hζ
  constructor
  · intro b
    have hx : IsPrimitiveRoot (ζ ^ (b : ZMod N).val) N := hζp.pow_of_coprime _ (ZMod.val_coe_unit_coprime b)
    have hmin : minpoly ℚ ζ = Polynomial.cyclotomic N ℚ := (Polynomial.cyclotomic_eq_minpoly_rat hζp hpos).symm
    have hev : Polynomial.aeval (ζ ^ (b : ZMod N).val) (minpoly ℚ ζ) = 0 := by
      rw [hmin, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
      exact Polynomial.isRoot_cyclotomic_iff.mpr hx
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic ζ) hev
    refine ⟨σ.toRingEquiv, fun x hxN => ?_⟩
    obtain ⟨k, -, rfl⟩ := hζp.eq_pow_of_pow_eq_one hxN
    show σ (ζ ^ k) = (ζ ^ k) ^ (b : ZMod N).val
    rw [map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]
  · intro σ
    have h1 : IsPrimitiveRoot (σ ζ) N := hζp.map_of_injective σ.injective
    obtain ⟨i, hi, hiζ⟩ := hζp.eq_pow_of_pow_eq_one h1.pow_eq_one
    have hcop : i.Coprime N := (hζp.pow_iff_coprime hpos i).mp (hiζ ▸ h1)
    refine ⟨ZMod.unitOfCoprime i hcop, fun x hxN => ?_⟩
    obtain ⟨k, -, rfl⟩ := hζp.eq_pow_of_pow_eq_one hxN
    rw [map_pow, ← hiζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hi, ← pow_mul, ← pow_mul, mul_comm]
