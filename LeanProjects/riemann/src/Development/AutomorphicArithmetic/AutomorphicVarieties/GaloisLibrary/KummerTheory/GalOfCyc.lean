import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.galOfCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (E K : Type) [Field E] [Field K] [Algebra E K] [Algebra E Ω] [Algebra K Ω] [IsScalarTower E K Ω] [IsCyclotomicExtension {l ^ n} E K], galOf F K Ω = levU l (galOf F E Ω) n := by
  intro F Ω _ _ _ _ _ l _ n E K _ _ _ _ _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  ext σ
  have key : ∀ t : Ω, t ^ (l ^ n) = 1 →
      σ t = t ^ ((cycZ F Ω l σ).val.toZModPow n).val := fun t ht =>
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω σ) t ht
  show σ ∈ galOf F K Ω ↔ σ ∈ galOf F E Ω ⊓ Subgroup.comap (cycZ F Ω l) (KStar.TotallyRealRoots.princ l n)
  rw [Subgroup.mem_inf, Subgroup.mem_comap, KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow]
  constructor
  · intro h
    have hE : σ ∈ galOf F E Ω := fun x => by
      have hx := h (algebraMap E K x)
      rwa [← IsScalarTower.algebraMap_apply] at hx
    refine ⟨hE, ?_⟩
    have hζ : IsPrimitiveRoot (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) (l ^ n) :=
      (IsCyclotomicExtension.zeta_spec (l ^ n) E K).map_of_injective (algebraMap K Ω).injective
    have h1 := key _ hζ.pow_eq_one
    rw [h (IsCyclotomicExtension.zeta (l ^ n) E K)] at h1
    have hfin : IsOfFinOrder (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) :=
      orderOf_pos_iff.mp (by rw [← hζ.eq_orderOf]; exact Nat.pos_of_neZero _)
    have e : (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) ^
        ((cycZ F Ω l σ).val.toZModPow n).val =
        (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) ^ 1 := by
      rw [pow_one]
      exact h1.symm
    have h3 : ((cycZ F Ω l σ).val.toZModPow n).val ≡ 1 [MOD l ^ n] := by
      have h5 := hfin.pow_eq_pow_iff_modEq.mp e
      rwa [← hζ.eq_orderOf] at h5
    ext
    have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h3
    rw [ZMod.natCast_zmod_val, Nat.cast_one] at h4
    simpa using h4
  · rintro ⟨hE, hc⟩
    have hc' : (cycZ F Ω l σ).val.toZModPow n = 1 := by
      have := congrArg Units.val hc
      simpa using this
    intro x
    let f1 : K →ₐ[E] Ω := IsScalarTower.toAlgHom E K Ω
    let f2 : K →ₐ[E] Ω :=
      { toRingHom := (σ : Ω →+* Ω).comp (algebraMap K Ω)
        commutes' := fun r => by
          show σ (algebraMap K Ω (algebraMap E K r)) = algebraMap E Ω r
          rw [← IsScalarTower.algebraMap_apply]
          exact hE r }
    have hx := IsCyclotomicExtension.adjoin_roots (S := {l ^ n}) (A := E) (B := K) x
    have hmem : x ∈ AlgHom.equalizer f1 f2 := by
      refine Algebra.adjoin_le (fun b hb => ?_) hx
      obtain ⟨m, hm, -, hbm⟩ := hb
      rw [Set.mem_singleton_iff] at hm
      subst hm
      have ht : (algebraMap K Ω b) ^ (l ^ n) = 1 := by rw [← map_pow, hbm, map_one]
      show algebraMap K Ω b = σ (algebraMap K Ω b)
      rw [key _ ht, hc', ZMod.val_one_eq_one_mod]
      conv_lhs => rw [← pow_one (algebraMap K Ω b), ← Nat.mod_add_div 1 (l ^ n), pow_add, pow_mul, ht, one_pow, mul_one]
    exact ((AlgHom.mem_equalizer f1 f2 x).mp hmem).symm
