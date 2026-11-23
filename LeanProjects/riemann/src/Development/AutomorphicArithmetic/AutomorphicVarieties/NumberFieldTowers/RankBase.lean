import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.GalTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DinfTransport

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem rb_len {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (e : M ≃ₗ[R] M') (a : R) :
    Module.length R (Submodule.torsionBy R M a) = Module.length R (Submodule.torsionBy R M' a) := by
  refine LinearEquiv.length_eq (e.ofSubmodules _ _ ?_)
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.mem_torsionBy_iff, Submodule.mem_torsionBy_iff,
    ← map_smul, map_eq_zero_iff _ e.injective]

private theorem rb_key (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (f : F →+* F') (σ : Ω ≃+* Ω')
    (h : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) (l : ℕ) [Fact l.Prime] (N : ℕ) (U V : Subgroup (G F Ω))
    (hV : ∀ g, g ∈ V ↔ ∀ y, g (σ.symm (algebraMap F' Ω' y)) = σ.symm (algebraMap F' Ω' y)) (hU : cycU l U = cycU l V) :
    xRank l N U = xRank l N (⊤ : Subgroup (G F' Ω')) := by
  obtain ⟨φ, -, hφ, hc, -, -⟩ := galTransport F Ω F' Ω' f σ h
  have hm : (cycU l (⊤ : Subgroup (G F' Ω'))).map φ = cycU l U := by
    rw [hU]
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      refine ⟨(hV _).2 fun y => σ.injective ?_, (hc l g').trans hg'.2⟩
      rw [hφ, RingEquiv.apply_symm_apply, AlgEquiv.commutes]
    · rintro ⟨h1, h2⟩
      let g' : G F' Ω' := AlgEquiv.ofRingEquiv (f := (σ.symm.trans g.toRingEquiv).trans σ) fun y => by
        show σ (g (σ.symm (algebraMap F' Ω' y))) = _
        rw [(hV g).1 h1 y, RingEquiv.apply_symm_apply]
      have e : φ g' = g := AlgEquiv.ext fun x => σ.injective (by
        rw [hφ]
        show σ (g (σ.symm (σ x))) = _
        rw [RingEquiv.symm_apply_apply])
      refine ⟨g', ⟨trivial, ?_⟩, e⟩
      exact (hc l g').symm.trans (e ▸ h2)
  obtain ⟨Ψ, -⟩ := dinfTransport F Ω F' Ω' f σ h φ hφ l N U ⊤ hm
  exact rb_len Ψ _

private theorem rb_one (k L Ω : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω] [Algebra k L]
    [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure k Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (N : ℕ)
    (U : Subgroup (G k Ω)) (hU : cycU l U = cycU l (galOf k L Ω)) : xRank l N U = rankN l L N := by
  let σ : Ω ≃ₐ[L] AlgebraicClosure L := IsAlgClosure.equiv L Ω (AlgebraicClosure L)
  have hs : ∀ y, σ.toRingEquiv.symm (algebraMap L _ y) = algebraMap L Ω y := fun y => σ.symm.commutes y
  refine rb_key k Ω L (AlgebraicClosure L) (algebraMap k L) σ.toRingEquiv (fun x => ?_) l N U _ (fun g => ?_) hU
  · rw [IsScalarTower.algebraMap_apply k L Ω]
    exact σ.commutes _
  · simp only [hs]
    exact Iff.rfl

theorem UpperTheory.V.Tower.rankBase :
    (∀ (k L Ω : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure k Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G k Ω)), cycU l U = cycU l (galOf k L Ω) → xRank l N U = rankN l L N) ∧
        (∀ (l : ℕ) [Fact l.Prime] (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'] (N : ℕ), Nonempty (L ≃+* L') → rankN l L N = rankN l L' N) ∧
        ∀ (l : ℕ) [Fact l.Prime] (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L'] (n N : ℕ), IsCyclotomicExtension {l ^ n} L L' → rankN l L' N = rankN l L N := by
  refine ⟨rb_one, ?_, ?_⟩
  · rintro l _ L L' _ _ _ _ N ⟨e⟩
    let σ := IsAlgClosure.equivOfEquiv (AlgebraicClosure L) (AlgebraicClosure L') e
    have h : ∀ x, σ (algebraMap L _ x) = algebraMap L' _ (e x) := fun x =>
      IsAlgClosure.equivOfEquiv_algebraMap _ _ e x
    refine rb_key L _ L' _ e.toRingHom σ h l N ⊤ ⊤ (fun g => ⟨fun _ y => ?_, fun _ => trivial⟩) rfl
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← h, RingEquiv.symm_apply_apply, AlgEquiv.commutes]
  · intro l _ L L' _ _ _ _ _ n N hc
    haveI : Algebra.IsAlgebraic L L' := Algebra.IsAlgebraic.tower_top (K := ℚ) L
    haveI : IsAlgClosure L (AlgebraicClosure L') := ⟨inferInstance, Algebra.IsAlgebraic.trans L L' _⟩
    have h := galOfCyc L (AlgebraicClosure L') l n L L'
    rw [← rb_one L L' (AlgebraicClosure L') l N ⊤ (by rw [h, cycU_levU, galOf_self]),
      rb_one L L (AlgebraicClosure L') l N ⊤ (by rw [galOf_self])]
