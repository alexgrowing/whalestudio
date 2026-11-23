import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LengthH0GlobalEqLevelGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem cls_eq_of {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {N : ℕ} [NeZero N] {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) (σ : G k Ω) (u : (ZMod N)ˣ)
    (h : σ ζ = ζ ^ (u : ZMod N).val) : cls k Ω N σ = u := by
  have h1 := cls_spec N σ ζ hζ.pow_eq_one
  rw [h1] at h
  apply Units.ext
  exact ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h)

private theorem aux (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N]
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K] :
    Function.Surjective (cls ℚ Ω N) ∧
      ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
        KStar.TotallyRealRoots.princ l (N.factorization l) ≤ (Ine (F := ℚ) A ⊓ (cls ℚ Ω N).ker).map (cycZ ℚ Ω l) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let ι : K →ₐ[ℚ] Ω := IsAlgClosed.lift
  letI : Algebra K Ω := ι.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := IsAlgClosure.mk ‹_› ‹_›
  have hζK := IsCyclotomicExtension.zeta_spec N ℚ K
  set ζ := IsCyclotomicExtension.zeta N ℚ K
  have hζ : IsPrimitiveRoot (algebraMap K Ω ζ) N :=
    hζK.map_of_injective (algebraMap K Ω).injective
  have hker : ∀ τ : G K Ω, cls ℚ Ω N (galEmb ℚ K Ω τ) = 1 := by
    intro τ
    apply cls_eq_of hζ
    have hτ : galEmb ℚ K Ω τ (algebraMap K Ω ζ) = algebraMap K Ω ζ := τ.commutes ζ
    rw [hτ, Units.val_one, ZMod.val_one_eq_one_mod]
    conv_lhs => rw [← pow_one (algebraMap K Ω ζ), ← Nat.mod_add_div 1 N, pow_add, pow_mul,
      hζ.pow_eq_one, one_pow, mul_one]
  refine ⟨?_, ?_⟩
  · intro u
    let χ : K ≃ₐ[ℚ] K := (IsCyclotomicExtension.Rat.galEquivZMod N K).symm u
    refine ⟨χ.liftNormal Ω, cls_eq_of hζ _ u ?_⟩
    rw [AlgEquiv.liftNormal_commutes,
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N K χ hζK.pow_eq_one]
    have hχ : IsCyclotomicExtension.Rat.galEquivZMod N K χ = u := MulEquiv.apply_symm_apply _ u
    rw [hχ, map_pow]
  · intro l _ A hA
    have hA' : A ≠ ⊤ := by
      intro h
      exact ((places K Ω l A).2.1 h).2 hA
    obtain ⟨v, hv⟩ := (places K Ω l A).1 hA'
    have hvl := ((places K Ω l A).2.2.1 v hv).mp hA
    have h1 := UpperTheory.V.LDataCardLeFinrank.princ_le_ineImage (F := K) (Ω := Ω) (N := N) (K := K)
      (AlgHom.id ℚ K) hvl hv
    refine h1.trans ?_
    unfold UpperTheory.V.LDataCardLeFinrank.ineImage
    have hfam := UpperTheory.V.Base.galEmbFam ℚ K Ω l
    rw [← hfam.2.2.1, ← Subgroup.map_map]
    apply Subgroup.map_mono
    rintro σ ⟨τ, hτ, rfl⟩
    refine ⟨?_, hker τ⟩
    have hI := (hfam.1 A).2
    rw [← hI] at hτ
    exact hτ

theorem UpperTheory.V.Chr.clsOnto :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N], Function.Surjective (cls ℚ Ω N) ∧
          ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
            KStar.TotallyRealRoots.princ l (N.factorization l) ≤ (Ine (F := ℚ) A ⊓ (cls ℚ Ω N).ker).map (cycZ ℚ Ω l) := by
  intro Ω _ _ _ N _
  exact aux Ω N (CyclotomicField N ℚ)
