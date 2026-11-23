import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

section General

variable {L : Type} [Field L] [NumberField L]

theorem conjPl_iff_comap (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ v.asIdeal = v'.asIdeal.comap (RingOfIntegers.mapRingEquiv c) := by
  constructor
  · intro h
    ext x
    have h1 : v'.valuation L (algebraMap (𝓞 L) L (RingOfIntegers.mapRingEquiv c x)) =
        v.valuation L (algebraMap (𝓞 L) L x) := h (algebraMap (𝓞 L) L x)
    rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L),
      ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L), h1]
  · intro h x
    exact (GlobalTheory.QNorm.valuation_of_eq_comap c v' v h x).symm

theorem conjPl_iff_mem (c : L ≃+* L) (v v' : HeightOneSpectrum (𝓞 L)) :
    ConjPl c v v' ↔ ∀ x y : 𝓞 L, (y : L) = c (x : L) → (x ∈ v.asIdeal ↔ y ∈ v'.asIdeal) := by
  rw [conjPl_iff_comap]
  constructor
  · intro h x y hxy
    have e : y = RingOfIntegers.mapRingEquiv c x := RingOfIntegers.ext hxy
    rw [h, Ideal.mem_comap, e]
  · intro h
    ext x
    exact h x (RingOfIntegers.mapRingEquiv c x) rfl

theorem existsUnique_conjPl (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)) : ∃! v', ConjPl c v v' := by
  set e : 𝓞 L ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv c with he
  refine ⟨v.comap (e.symm : 𝓞 L →+* 𝓞 L) e.symm.surjective, ?_, ?_⟩
  · show ConjPl c v _
    rw [conjPl_iff_comap]
    ext x
    change x ∈ v.asIdeal ↔ e.symm (e x) ∈ v.asIdeal
    rw [e.symm_apply_apply]
  · intro v' h
    rw [conjPl_iff_comap] at h
    ext x
    change x ∈ v'.asIdeal ↔ e.symm x ∈ v.asIdeal
    rw [h, Ideal.mem_comap, e.apply_symm_apply]

theorem under_eq_iff_conjPl {F : Type} [Field F] [NumberField F] [Algebra F L] (c : L ≃ₐ[F] L)
    (hr : Module.finrank F L = 2) (hc : c ≠ 1) (w w' : HeightOneSpectrum (𝓞 L)) :
    w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') := by
  have : Algebra.IsQuadraticExtension F L := { finrank_eq_two' := hr }
  have : IsGalois F L := inferInstance
  have hall : ∀ σ : L ≃ₐ[F] L, σ = 1 ∨ σ = c := by
    intro σ
    have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, hr]
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).1 hcard
    by_cases h : σ = 1
    · exact Or.inl h
    · exact Or.inr ((hy σ h).trans (hy c hc).symm)
  constructor
  · intro hu
    have := w.isPrime
    have := w'.isPrime
    have hu' : w'.asIdeal.under (𝓞 F) = w.asIdeal.under (𝓞 F) := congrArg HeightOneSpectrum.asIdeal hu
    obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F L (𝓞 L) (p := w.asIdeal.under (𝓞 F))
      (P₁ := w'.asIdeal) (P₂ := w.asIdeal) ⟨inferInstance, ⟨hu'.symm⟩⟩ ⟨inferInstance, ⟨rfl⟩⟩
    rcases hall σ with rfl | rfl
    · left
      ext x
      rw [← hσ, map_one, Ideal.mem_comap]
      rfl
    · right
      rw [conjPl_iff_mem]
      intro x y hxy
      have e : y = galRestrict (𝓞 F) F L (𝓞 L) σ x := by
        apply RingOfIntegers.ext
        rw [hxy]
        exact (algebraMap_galRestrict_apply (𝓞 F) σ x).symm
      rw [← hσ, Ideal.mem_comap, e]
  · rintro (rfl | h)
    · rfl
    · rw [conjPl_iff_mem] at h
      ext a
      exact (h (algebraMap (𝓞 F) (𝓞 L) a) (algebraMap (𝓞 F) (𝓞 L) a) (c.commutes (a : F)).symm).symm

end General

open Classical in

theorem conjPl_main : (∀ (L : Type) [Field L] [NumberField L] (c : L ≃+* L) (v : HeightOneSpectrum (𝓞 L)), ∃! v', ConjPl c v v') ∧ (∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (w w' : HeightOneSpectrum (𝓞 H.E)), IsConjPl H w w' ↔ ConjPl H.conj.toRingEquiv w w') ∧ ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L), Module.finrank F L = 2 → c ≠ 1 → ∀ (w w' : HeightOneSpectrum (𝓞 L)), w'.under (𝓞 F) = w.under (𝓞 F) ↔ (w' = w ∨ ConjPl c.toRingEquiv w w') :=
  ⟨fun _ _ _ c v => existsUnique_conjPl c v,
    fun _ H w w' => (conjPl_iff_mem H.conj.toRingEquiv w w').symm,
    fun _ _ _ _ _ _ _ c hr hc w w' => under_eq_iff_conjPl c hr hc w w'⟩

end GlobalTheory.Mem.Chr
