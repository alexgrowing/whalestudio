import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem card_simple (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    [h : IsSimpleModule O M] : Nat.card M = Nat.card (ResidueField O) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp h
  obtain rfl : I = maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
  exact Nat.card_congr e.toEquiv

private theorem card_of_finiteLength (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M]
    [Module O M] (h : IsFiniteLength O M) :
    ∃ k : ℕ, Module.length O M = k ∧ Nat.card M = Nat.card (ResidueField O) ^ k := by
  induction h with
  | of_subsingleton =>
    refine ⟨0, Module.length_eq_zero, ?_⟩
    rw [pow_zero]
    exact Nat.card_of_subsingleton 0
  | @of_simple_quotient M _ _ N _ hS ih =>
    obtain ⟨k, hk, hc⟩ := ih
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      norm_cast
    · have hq : Nat.card (M ⧸ N) = Nat.card (ResidueField O) := card_simple O (M ⧸ N)
      have hsplit := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
      change Nat.card M = Nat.card (M ⧸ N) * Nat.card N at hsplit
      rw [hsplit, hq, hc, pow_succ, mul_comm]

theorem UpperTheory.V.X.So.cardLen :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], 1 < Nat.card (ResidueField O) ∧ ∀ (N : Type) [AddCommGroup N] [Module O N], (Module.length O N ≠ ⊤ ↔ Finite N) ∧ (Finite N → Nat.card N = Nat.card (ResidueField O) ^ (Module.length O N).toNat) := by
  intro l _ O _ _ _ _ _
  have : CharZero O := charZero_of_injective_algebraMap (UpperTheory.V.Base.dvrFacts l O).1
  have hres : Finite (ResidueField O) := (UpperTheory.V.abelian₂.dvr_finite l O).2.1
  have h1 : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
  refine ⟨h1, fun N _ _ => ?_⟩
  have hfl : Finite N → IsFiniteLength O N := fun _ =>
    isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  refine ⟨⟨fun h => ?_, fun h => Module.length_ne_top_iff.2 (hfl h)⟩, fun h => ?_⟩
  · obtain ⟨k, -, hk⟩ := card_of_finiteLength O N (Module.length_ne_top_iff.1 h)
    exact Nat.finite_of_card_ne_zero (hk ▸ pow_ne_zero k (by omega))
  · obtain ⟨k, hk1, hk⟩ := card_of_finiteLength O N (hfl h)
    rw [hk, hk1, ENat.toNat_coe]
