import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.LocallyExactCech
import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyHoldsOfForallAndMonoAndInterAndPullback

open CategoryTheory Limits AlgebraicGeometry Opposite UpperTheory.Et

private theorem UpperTheory.locally_of_etale_cover (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g))
    (h : ∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U), Etale g ∧ x ∈ Set.range g ∧ P V g) :
    LocT Scheme.etaleTopology U P := by
  choose V g hg hx hP' using h
  refine ⟨Sieve.ofArrows V g, ?_, ?_⟩
  · exact Precoverage.generate_mem_toGrothendieck
      ((Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ⟨x, hx x⟩, hg⟩)
  · rintro W f ⟨Y, k, _, ⟨i⟩, rfl⟩
    exact hP _ _ _ _ (hP' i)

theorem UpperTheory.etaleLocallyHolds_of_pointwise_cover_or_affine_local :
    ∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g)) →
    ((∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U), Etale g ∧ x ∈ Set.range g ∧ P V g) → LocT Scheme.etaleTopology U P) ∧
    ((∀ (A : CommRingCat.{0}) (g : Spec A ⟶ U), LocT Scheme.etaleTopology (Spec A) fun V k => P V (k ≫ g)) → LocT Scheme.etaleTopology U P) := by
  intro U P hP
  refine ⟨UpperTheory.locally_of_etale_cover U P hP, fun hA => ?_⟩
  obtain ⟨-, -, -, h4, h5, -⟩ := UpperTheory.locallyHolds_of_forall_and_mono_and_inter_and_pullback Scheme.etaleTopology
  apply h5
  apply UpperTheory.locally_of_etale_cover U _
  · intro V W g k hV
    simpa only [Category.assoc] using h4 V W k _ hV
  · intro x
    exact ⟨_, U.affineCover.f (U.affineCover.idx x), inferInstance,
      U.affineCover.covers x, hA _ _⟩
