import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsClosedImmersionDescendsToSubringStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem locallyOfFinitePresentation_pspace_str (R : Type) [CommRing R] (N : ℕ) :
    LocallyOfFinitePresentation (PSpace.str R N) := by
  have hloc : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
  refine IsZariskiLocalAtSource.of_openCover (ProjSpace.chartCover R N) fun (i : Fin (N + 1)) => ?_
  change LocallyOfFinitePresentation (ProjSpace.chartι R N i ≫ PSpace.str R N)
  rw [ProjSpace.chartι_str]
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial {j // j ≠ i} R)))
  rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom, ← MvPolynomial.algebraMap_eq,
    RingHom.finitePresentation_algebraMap]
  infer_instance

theorem isProjOver_descends_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFiniteType f₀], IsPullback π f f₀ (spMap R₀.subtype) → IsProjOver f → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → IsProjOver f₁ := by
  intro S _ R₀ X X₀ f f₀ π _ _ _ hX hP
  classical
  have hsub : ∀ {A B : Subring S} (hAB : A ≤ B), B.subtype.comp (Subring.inclusion hAB) = A.subtype :=
    fun _ => RingHom.ext fun _ => rfl
  have hincl : ∀ {A B C : Subring S} (hAB : A ≤ B) (hBC : B ≤ C) (hAC : A ≤ C),
      (Subring.inclusion hBC).comp (Subring.inclusion hAB) = Subring.inclusion hAC :=
    fun _ _ _ => RingHom.ext fun _ => rfl
  have hsp : ∀ {A B : Subring S} (hAB : A ≤ B),
      spMap B.subtype ≫ spMap (Subring.inclusion hAB) = spMap A.subtype := by
    intro A B hAB
    rw [← spMap_comp, hsub]
  have hsp2 : ∀ {A B C : Subring S} (hAB : A ≤ B) (hBC : B ≤ C) (hAC : A ≤ C),
      spMap (Subring.inclusion hBC) ≫ spMap (Subring.inclusion hAB) = spMap (Subring.inclusion hAC) := by
    intro A B C hAB hBC hAC
    rw [← spMap_comp, hincl]
  obtain ⟨L, -, M, s, hv⟩ := (ProjSpace.isProjBy_iff_isProjOver f).2 hP
  obtain ⟨hs, hci⟩ := (ProjSpace.veryAmpleBy_iff f s).1 hv
  set i := ProjSpace.toProj f s hs with hi
  have hif : i ≫ PSpace.str S M = f := ProjSpace.toProj_str f s hs
  have : LocallyOfFinitePresentation (PSpace.str R₀ M) := locallyOfFinitePresentation_pspace_str R₀ M
  have hφ : (i ≫ ProjSpace.baseChange M R₀.subtype) ≫ PSpace.str R₀ M = π ≫ f₀ := by
    rw [Category.assoc, ProjSpace.baseChange_str, ← Category.assoc, hif, hX.w]
  obtain ⟨F₁, hF₁⟩ := morphism_descends_to_subring S R₀ X X₀ (PSpace R₀ M) f f₀ (PSpace.str R₀ M) π
    (i ≫ ProjSpace.baseChange M R₀.subtype) hX hφ
  set R₀' : Subring S := R₀ ⊔ Subring.closure (F₁ : Set S) with hR₀'
  have h₀ : R₀ ≤ R₀' := le_sup_left
  have hF₁' : (F₁ : Set S) ⊆ R₀' := fun x hx =>
    (le_sup_right : Subring.closure (F₁ : Set S) ≤ R₀') (Subring.subset_closure hx)
  obtain ⟨X₀', π₀', f₀', hX₀'⟩ : ∃ (X₀' : Scheme.{0}) (π₀' : X₀' ⟶ X₀) (f₀' : X₀' ⟶ Sp R₀'),
      IsPullback π₀' f₀' f₀ (spMap (Subring.inclusion h₀)) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨j, hjπ, hjf⟩ : ∃ j : X ⟶ X₀', j ≫ π₀' = π ∧ j ≫ f₀' = f ≫ spMap R₀'.subtype :=
    ⟨hX₀'.lift π (f ≫ spMap R₀'.subtype) (by rw [Category.assoc, hsp h₀, hX.w]),
      hX₀'.lift_fst _ _ _, hX₀'.lift_snd _ _ _⟩
  obtain ⟨ψ, hjψ, hψq⟩ := hF₁ R₀' h₀ hF₁' X₀' f₀' π₀' j hX₀' hjπ hjf
  have hbc₀ := ProjSpace.isPullback_baseChange M (Subring.inclusion h₀)
  obtain ⟨g₀, hg₀b, hg₀q⟩ : ∃ g₀ : X₀' ⟶ PSpace R₀' M,
      g₀ ≫ ProjSpace.baseChange M (Subring.inclusion h₀) = ψ ∧ g₀ ≫ PSpace.str R₀' M = f₀' :=
    ⟨hbc₀.lift ψ f₀' (by rw [hψq, hX₀'.w]), hbc₀.lift_fst _ _ _, hbc₀.lift_snd _ _ _⟩
  have : IsProper (PSpace.str R₀' M) := isProper_str R₀' M
  have : QuasiCompact f₀' := MorphismProperty.of_isPullback (P := @QuasiCompact) hX₀' inferInstance
  have : QuasiSeparated f₀' := MorphismProperty.of_isPullback (P := @QuasiSeparated) hX₀' inferInstance
  have : LocallyOfFiniteType f₀' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hX₀' inferInstance
  have : LocallyOfFiniteType (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : QuasiSeparated (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : QuasiCompact (g₀ ≫ PSpace.str R₀' M) := by rw [hg₀q]; infer_instance
  have : LocallyOfFiniteType g₀ := locallyOfFiniteType_of_comp g₀ (PSpace.str R₀' M)
  have : QuasiSeparated g₀ := QuasiSeparated.of_comp g₀ (PSpace.str R₀' M)
  have : QuasiCompact g₀ := QuasiCompact.of_comp g₀ (PSpace.str R₀' M)
  have hY := ProjSpace.isPullback_baseChange M R₀'.subtype
  have hbc : ProjSpace.baseChange M R₀'.subtype ≫ ProjSpace.baseChange M (Subring.inclusion h₀) =
      ProjSpace.baseChange M R₀.subtype := by
    rw [← ProjSpace.baseChange_comp, hsub]
  have hleft : IsPullback j f f₀' (spMap R₀'.subtype) := by
    refine IsPullback.of_right ?_ hjf hX₀'
    rw [hjπ, hsp h₀]
    exact hX
  have hsq : IsPullback j i g₀ (ProjSpace.baseChange M R₀'.subtype) := by
    refine IsPullback.of_bot ?_ ?_ hY
    · rw [hif, hg₀q]
      exact hleft
    · apply hbc₀.hom_ext
      · rw [Category.assoc, hg₀b, hjψ, Category.assoc, hbc]
      · rw [Category.assoc, hg₀q, hjf, Category.assoc, ProjSpace.baseChange_str, ← Category.assoc, hif]
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.isClosedImmersion_descends_to_subring' S R₀' X₀' (PSpace R₀' M) X (PSpace S M) g₀ (PSpace.str R₀' M)
    i j (ProjSpace.baseChange M R₀'.subtype) (PSpace.str S M) hY hsq hci
  refine ⟨F₁ ∪ F₂, fun R₁ h hF X₁ f₁ π₁ hX₁ => ?_⟩
  have h' : R₀' ≤ R₁ := sup_le h (Subring.closure_le.2 fun x hx =>
    hF (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx))))
  have hF₂' : (F₂ : Set S) ⊆ R₁ := fun x hx =>
    hF (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hx)))
  obtain ⟨πX₁, hπ₁, hf₁⟩ : ∃ πX₁ : X₁ ⟶ X₀',
      πX₁ ≫ π₀' = π₁ ∧ πX₁ ≫ f₀' = f₁ ≫ spMap (Subring.inclusion h') :=
    ⟨hX₀'.lift π₁ (f₁ ≫ spMap (Subring.inclusion h')) (by rw [Category.assoc, hsp2 h₀ h' h, hX₁.w]),
      hX₀'.lift_fst _ _ _, hX₀'.lift_snd _ _ _⟩
  have hleft₁ : IsPullback πX₁ f₁ f₀' (spMap (Subring.inclusion h')) := by
    refine IsPullback.of_right ?_ hf₁ hX₀'
    rw [hπ₁, hsp2 h₀ h' h]
    exact hX₁
  have hY₁ := ProjSpace.isPullback_baseChange M (Subring.inclusion h')
  obtain ⟨g₁, hg₁b, hg₁q⟩ : ∃ g₁ : X₁ ⟶ PSpace R₁ M,
      g₁ ≫ ProjSpace.baseChange M (Subring.inclusion h') = πX₁ ≫ g₀ ∧ g₁ ≫ PSpace.str R₁ M = f₁ :=
    ⟨hY₁.lift (πX₁ ≫ g₀) f₁ (by rw [Category.assoc, hg₀q, hf₁]), hY₁.lift_fst _ _ _,
      hY₁.lift_snd _ _ _⟩
  have hsq₁ : IsPullback πX₁ g₁ g₀ (ProjSpace.baseChange M (Subring.inclusion h')) := by
    refine IsPullback.of_bot ?_ hg₁b.symm hY₁
    rw [hg₁q, hg₀q]
    exact hleft₁
  have := hF₂ R₁ h' hF₂' X₁ (PSpace R₁ M) g₁ πX₁ (ProjSpace.baseChange M (Subring.inclusion h'))
    (PSpace.str R₁ M) hY₁ hsq₁
  rw [← hg₁q]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion g₁ (ProjSpace.isProjOver_pspace_str R₁ M)

end GlobalTheory
