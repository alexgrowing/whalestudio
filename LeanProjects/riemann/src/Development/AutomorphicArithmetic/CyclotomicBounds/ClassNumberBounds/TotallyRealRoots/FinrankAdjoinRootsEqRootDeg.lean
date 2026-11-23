import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalOpen
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuFinite
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuBasic
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.NCField

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem cyclotomicCharacter_eq_of_ringEquiv_conj {L M : Type*} [Field L] [Field M] (p : ℕ)
    [Fact p.Prime] (φ : L ≃+* M) (g : L ≃+* L) (g' : M ≃+* M) (h : ∀ x, g' (φ x) = φ (g x)) :
    cyclotomicCharacter M p g' = cyclotomicCharacter L p g := by
  have hg' : g' = φ.symm.trans (g.trans φ) := by
    ext x
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, ← h, RingEquiv.apply_symm_apply]
  subst hg'
  symm
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

theorem cyclotomicCharacter_conj {Ω Ω' : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field Ω']
    [CharZero Ω'] [IsAlgClosed Ω'] (e : Ω ≃+* Ω') (g : Ω ≃+* Ω) (g' : Ω' ≃+* Ω')
    (h : ∀ x, g' (e x) = e (g x)) :
    cyclotomicCharacter Ω' l g' = cyclotomicCharacter Ω l g := cyclotomicCharacter_eq_of_ringEquiv_conj l e g g' h

theorem mem_galImage_iff_of_equiv {E E' : Type*} [Field E] [CharZero E] [Field E'] (f : E ≃+* E')
    (Ω : Type*) [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω] (u : ℤ_[l]ˣ) :
    u ∈ galImage l E ↔ ∃ g : Ω ≃ₐ[E'] Ω, cyclotomicCharacter Ω l g.toRingEquiv = u := by
  let ε := IsAlgClosure.equivOfEquiv (AlgebraicClosure E) Ω f
  have hε : ∀ s : E, ε (algebraMap E (AlgebraicClosure E) s) = algebraMap E' Ω (f s) :=
    IsAlgClosure.equivOfEquiv_algebraMap _ _ f
  have hε' : ∀ r : E',
      ε.symm (algebraMap E' Ω r) = algebraMap E (AlgebraicClosure E) (f.symm r) :=
    IsAlgClosure.equivOfEquiv_symm_algebraMap _ _ f
  simp only [galImage, MonoidHom.mem_range]
  constructor
  · rintro ⟨σ, rfl⟩
    let gr : Ω ≃+* Ω := ε.symm.trans (σ.toRingEquiv.trans ε)
    refine ⟨AlgEquiv.ofRingEquiv (f := gr) fun r ↦ ?_, ?_⟩
    · simp only [gr, RingEquiv.trans_apply, hε', AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, hε,
        RingEquiv.apply_symm_apply]
    · simp only [eps, MonoidHom.comp_apply]
      apply cyclotomicCharacter_eq_of_ringEquiv_conj l ε
      intro x
      simp [gr, MulSemiringAction.toRingAut_apply, AlgEquiv.smul_def]
  · rintro ⟨g, rfl⟩
    let sr := ε.trans (g.toRingEquiv.trans ε.symm)
    refine ⟨AlgEquiv.ofRingEquiv (f := sr) fun s ↦ ?_, ?_⟩
    · simp [sr, hε, hε']
    · simp only [eps, MonoidHom.comp_apply]
      symm
      apply cyclotomicCharacter_eq_of_ringEquiv_conj l ε
      intro x
      simp [sr, MulSemiringAction.toRingAut_apply, AlgEquiv.smul_def]

end KStar.TotallyRealRoots
