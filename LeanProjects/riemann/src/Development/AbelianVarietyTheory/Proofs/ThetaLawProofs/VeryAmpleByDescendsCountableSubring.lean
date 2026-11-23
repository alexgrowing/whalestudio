import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCountableLocalPidSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetIsProjOverDescends
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory

open ProjSpace in

theorem exists_finset_isPullback_toImage_baseChange (R : Type) [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}}
    {N : ℕ} (e : X ⟶ PSpace R N) [IsClosedImmersion e] :
    ∃ c : Finset R, ∀ R₀ : Subring R, (c : Set R) ⊆ R₀ →
      IsPullback (e ≫ baseChange N R₀.subtype).toImage (e ≫ PSpace.str R N)
        ((e ≫ baseChange N R₀.subtype).imageι ≫ PSpace.str R₀ N) (spMap R₀.subtype) := by
  classical
  have hT : ∀ i : Fin (N + 1), ∃ T : Finset (MvPolynomial {j // j ≠ i} R),
      Ideal.span (chartAlgEquiv R N i '' T) = e.ker.ideal ⟨_, isAffineOpen_chart R N i⟩ := fun i => by
    obtain ⟨T, hT⟩ := (IsNoetherian.noetherian
      ((e.ker.ideal ⟨_, isAffineOpen_chart R N i⟩).comap (chartAlgEquiv R N i)))
    refine ⟨T, ?_⟩
    have := congrArg (Ideal.map (chartAlgEquiv R N i)) hT
    rw [Ideal.map_comap_of_surjective _ (chartAlgEquiv R N i).surjective] at this
    rw [← this]
    exact (Ideal.map_span _ _).symm
  choose T hT using hT
  refine ⟨Finset.univ.biUnion fun i => (T i).biUnion MvPolynomial.coeffs, fun R₀ hs => ?_⟩
  have key := comap_map_baseChange N R₀.subtype e.ker (fun i => T i) hT fun i t ht => by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.2
    intro c hc
    refine ⟨⟨c, hs ?_⟩, rfl⟩
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ i, t, ht, hc⟩
  rw [Scheme.IdealSheafData.map_ker] at key
  have h := isPullback_of_isClosedImmersion e (e ≫ baseChange N R₀.subtype).imageι
    (e ≫ baseChange N R₀.subtype).toImage (baseChange N R₀.subtype) (by simp)
    (by rw [← key]; congr 1; exact Scheme.IdealSheafData.ker_subschemeι _)
  exact h.flip.paste_vert (isPullback_baseChange N R₀.subtype)

open ProjSpace in

theorem veryAmpleBy_descends_countable_subring : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Flat f] (H : LB X) (m : ℕ) (s : Fin (m + 1) → H.Sec) (S : Set R), H.IsLB → VeryAmpleBy f H s → S.Countable → ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) (H₀ : LB X₀) (s₀ : Fin (m + 1) → H₀.Sec), Countable R₀ ∧ S ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ Module.FaithfullyFlat R₀ R ∧ IsPullback π f f₀ (spMap R₀.subtype) ∧ Flat f₀ ∧ H₀.IsLB ∧ VeryAmpleBy f₀ H₀ s₀ ∧ LBIso H (H₀.pull π) := by
  intro R _ _ _ _ X f hf H m s S hH hs hS
  obtain ⟨hs, he⟩ := (veryAmpleBy_iff f s).1 hs
  obtain ⟨c, hc⟩ := exists_finset_isPullback_toImage_baseChange R (toProj f s hs)
  obtain ⟨R₀, i₁, i₂, h₁, h₂, h₃, h₄⟩ := GlobalTheory.exists_countable_local_pid_subring R (S ∪ c) (hS.union c.countable_toSet)
  have hp := hc R₀ (Set.subset_union_right.trans h₂)
  rw [toProj_str] at hp
  have hσ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap R₀.subtype) := by
    have h : RingHom.FaithfullyFlat (CommRingCat.ofHom R₀.subtype).hom :=
      RingHom.faithfullyFlat_algebraMap_iff.2 h₄
    rw [← flat_and_surjective_SpecMap_iff] at h
    exact ⟨⟨h.2, h.1⟩, inferInstance⟩
  have := flat_descendsAlong_fpqc
  have hL := O1_isLB R₀ m
  refine ⟨R₀, i₁, i₂, _, _, _, _, _, h₁, Set.subset_union_left.trans h₂, h₃, h₄, hp,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) hp.flip hσ hf,
    LB.isLB_pull hL _, veryAmpleBy_secPull_coord _, ?_⟩
  refine LBIso.trans hH (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull hL _) _)
    (lbIso_pullback_O1_toProj (f ≫ spMap R₀.subtype) s hs).symm (GenSpread.lbIso_pull_pull hL _ ?_)
  rw [Scheme.Hom.toImage_imageι, toProj_baseChange]

end GlobalTheory
