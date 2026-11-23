import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.FinrankAdjoinRootsEqRootDeg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem cyclotomicCharacter_conj_ringEquiv {L M : Type} [Field L] [Field M] (p : ℕ) [Fact p.Prime]
    (φ : L ≃+* M) (g : L ≃+* L) :
    cyclotomicCharacter L p g = cyclotomicCharacter M p (φ.symm.trans (g.trans φ)) := by
  by_cases H : ∀ i : ℕ, ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i)
  · have hL (i : ℕ) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
    have hM (i : ℕ) : HasEnoughRootsOfUnity M (p ^ i) := by
      obtain ⟨ζ, hζ⟩ := H i
      exact ⟨⟨φ ζ, hζ.map_of_injective φ.injective⟩, rootsOfUnity.isCyclic _ _⟩
    ext1
    refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
    rw [cyclotomicCharacter.toZModPow, cyclotomicCharacter.toZModPow]
    refine modularCyclotomicCharacter.unique M
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity M (p ^ n)) _ fun t ht ↦ ?_
    have hs : Units.map φ.symm.toMonoidHom t ∈ rootsOfUnity (p ^ n) L := by
      rw [mem_rootsOfUnity] at ht ⊢
      rw [← map_pow, ht, map_one]
    have key := modularCyclotomicCharacter.spec L
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n)) g hs
    simp only [Units.coe_map, Units.val_pow_eq_pow_val] at key
    change g (φ.symm (t : M)) = (φ.symm (t : M)) ^ _ at key
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, key, map_pow, RingEquiv.apply_symm_apply]
  · have H' : ¬ ∀ i : ℕ, ∃ ζ : M, IsPrimitiveRoot ζ (p ^ i) := by
      intro hM
      apply H
      intro i
      obtain ⟨ζ, hζ⟩ := hM i
      exact ⟨φ.symm ζ, hζ.map_of_injective φ.symm.injective⟩
    ext1
    simp [cyclotomicCharacter, cyclotomicCharacter.toFun, H, H']

theorem UpperTheory.V.LDataCardLeFinrank.ranges :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l), (cycZ F Ω l).range = KStar.TotallyRealRoots.galImage l F ∧ D.chi.range = KStar.TotallyRealRoots.galImage l F ∧ ∀ v : D.S, (D.chi.comp (locFam D.S D.A v)).range = decImage F l (D.A v) := by
  intro F Ω _ _ _ _ _ l _ D
  have hcyc : (cycZ F Ω l).range = KStar.TotallyRealRoots.galImage l F := by
    let e : Ω ≃ₐ[F] AlgebraicClosure F := IsAlgClosure.equiv F Ω (AlgebraicClosure F)
    have hpt : ∀ σ : Gal(Ω/F), cycZ F Ω l σ = KStar.TotallyRealRoots.eps l F (AlgEquiv.autCongr e σ) := by
      intro σ
      simp only [cycZ, KStar.TotallyRealRoots.eps, MonoidHom.comp_apply]
      exact cyclotomicCharacter_conj_ringEquiv l e.toRingEquiv _
    ext x
    simp only [MonoidHom.mem_range, KStar.TotallyRealRoots.galImage]
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨_, (hpt σ).symm⟩
    · rintro ⟨τ, rfl⟩
      exact ⟨(AlgEquiv.autCongr e).symm τ, by rw [hpt, MulEquiv.apply_symm_apply]⟩
  have hchi : D.chi.range = (cycZ F Ω l).range := by
    have htop : (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    rw [← D.hchi, MonoidHom.range_comp, htop, ← MonoidHom.range_eq_map]
  refine ⟨hcyc, hchi.trans hcyc, fun v ↦ ?_⟩
  have hcomp : D.chi.comp (locFam D.S D.A v) = (cycZ F Ω l).comp (Dec (D.A v)).subtype := by
    rw [← D.hchi]
    rfl
  rw [hcomp, MonoidHom.range_comp, Subgroup.range_subtype]
  rfl
