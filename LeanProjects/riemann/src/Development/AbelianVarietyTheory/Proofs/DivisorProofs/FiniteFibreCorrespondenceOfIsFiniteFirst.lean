import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.FibreCrit

theorem exists_generization_mem {Y : Scheme.{0}} [IsLocallyNoetherian Y] {O : Set Y} (hO : IsOpen O)
    (hd : Dense O) (y : Y) : ∃ e0 : Y, e0 ⤳ y ∧ e0 ∈ O := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := y) trivial
  have : IsAffine U := hU
  have : IsNoetherian U.toScheme := {}
  obtain ⟨y', rfl⟩ : y ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hyU
  have hC := irreducibleComponent_mem_irreducibleComponents y'
  obtain ⟨o, ho, hne, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨_, ⟨w, hwo, rfl⟩, hwO⟩ :=
    hd.inter_open_nonempty _ (U.ι.isOpenEmbedding.isOpenMap _ ho) (hne.image _)
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  exact ⟨U.ι hC.1.genericPoint, (hg.specializes mem_irreducibleComponent).map U.ι.continuous,
    ((hg.specializes (hoC hwo)).map U.ι.continuous).mem_open hO hwO⟩

theorem spMap_algebraMap_apply (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (p : Sp K) : spMap (algebraMap V K) p = (⊥ : PrimeSpectrum V) := by
  refine PrimeSpectrum.ext ?_
  show Ideal.comap (algebraMap V K) p.asIdeal = ⊥
  rw [(Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V K)

end GlobalTheory.FibreCrit

namespace GlobalTheory.FibreCrit

theorem finite_fibre_of_isFinite : ∀ (X Y₀ Y : Scheme.{0}) (s t : Y ⟶ X) (i : Y₀ ⟶ Y), IsFinite s → IsOpenImmersion i → IsDominant i → IsLocallyNoetherian Y → (∀ z : X, {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ i ≫ s ∧ spMap (algebraMap V K) ≫ z' = x ≫ i ≫ t ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite) → ∀ z : X, {y : Y | t y = z}.Finite := by
  intro X Y₀ Y s t i hs hi hd hY hfin z
  refine (s.finite_preimage (hfin z)).subset ?_
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  obtain ⟨e0, he0y, he0i⟩ := exists_generization_mem i.isOpenEmbedding.isOpen_range i.denseRange y
  obtain ⟨V, _, _, _, g, hg0, hg1⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V)
      (_ : IsDiscreteValuationRing V) (g : Sp V ⟶ Y),
      g (⊥ : PrimeSpectrum V) ∈ Set.range i ∧ g (IsLocalRing.closedPoint V) = y := by
    by_cases he : e0 = y
    · subst he
      have hpt : ∀ q, (spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) ≫
          Y.fromSpecResidueField e0) q = e0 := fun q => by
        have h := Set.mem_range_self (f := Y.fromSpecResidueField e0)
          (spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) q)
        rw [Scheme.range_fromSpecResidueField] at h
        rw [Scheme.Hom.comp_apply]
        exact h
      exact ⟨PowerSeries (Y.residueField e0), inferInstance, inferInstance, inferInstance,
        spMap (algebraMap (Y.residueField e0) (PowerSeries (Y.residueField e0))) ≫
          Y.fromSpecResidueField e0, (hpt _).symm ▸ he0i, hpt _⟩
    · obtain ⟨O, hO, hV, -, f, hf0, hf1⟩ :=
        GlobalTheory.exists_complete_discreteValuationRing_of_specializes he0y he
      exact ⟨O, inferInstance, hO, hV, f, hf0 ▸ he0i, hf1⟩
  have hr : Set.range (spMap (algebraMap V (FractionRing V)) ≫ g) ⊆ Set.range i := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply, spMap_algebraMap_apply V (FractionRing V) q]
    exact hg0
  refine ⟨V, FractionRing V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, g ≫ s, g ≫ t, IsOpenImmersion.lift i _ hr, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (· ≫ s) (IsOpenImmersion.lift_fac i _ hr)).symm.trans (Category.assoc _ _ _)
  · exact (congrArg (· ≫ t) (IsOpenImmersion.lift_fac i _ hr)).symm.trans (Category.assoc _ _ _)
  · exact (Scheme.Hom.comp_apply g s _).trans (congrArg s hg1)
  · exact ((Scheme.Hom.comp_apply g t _).trans (congrArg t hg1)).trans hy

end GlobalTheory.FibreCrit
