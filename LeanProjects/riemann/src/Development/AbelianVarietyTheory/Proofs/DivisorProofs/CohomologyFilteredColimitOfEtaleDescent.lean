import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyInjectiveOfIsoOnFiniteTypeRingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveOfIsoOnFiniteTypeApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanQuasiIsoOfLocalQuasiIsoBoundedBelowDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCohomologyCommutesWithFilteredColimitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilteredColimitCohomologyTransportQuasiIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsAddCommGrpIffElementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoalternatingExactOfFiniteTypeIsoFilteredColimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreservesFilteredColimitsIsoOnFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringsRefineOfCechConervePropertyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ContAlg

theorem cohomology_filteredColimit_of_descent :
    ∀ (M : CommRingCat.{0} ⥤ AbCx) (F0 : CommRingCat.{0} ⥤ AddCommGrpCat.{1}) (ι : F0 ⟶ term M 0), PreservesFilteredColimitsOfSize.{0, 0} F0 → (∀ A, Function.Injective (ι.app A) ∧ ∀ z : (M.obj A).X 0, (M.obj A).d 0 (0 + 1) z = 0 ↔ ∃ x, ι.app A x = z) → (∀ n : ℤ, n < 0 → ∀ A, IsZero ((M.obj A).X n)) → (∀ n : ℤ, 0 < n → ∀ (A : CommRingCat.{0}) (z : (M.obj A).X n), (M.obj A).d n (n + 1) z = 0 → ∃ (B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ∧ ∃ y : (M.obj B).X (n - 1), (M.obj B).d (n - 1) n y = (M.map g).f n z) → (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∀ n, WExact (term M n) (coAug g)) → (∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ z : ((M).obj c.pt).X n, ((M).obj c.pt).d n (n + 1) z = 0 → ∃ (j : J) (w : ((M).obj (D.obj j)).X n) (y : ((M).obj c.pt).X (n - 1)), ((M).obj (D.obj j)).d n (n + 1) w = 0 ∧ ((M).map (c.ι.app j)).f n w = z + ((M).obj c.pt).d (n - 1) n y) ∧ ∀ (j : J) (w : ((M).obj (D.obj j)).X n), ((M).obj (D.obj j)).d n (n + 1) w = 0 → (∃ y : ((M).obj c.pt).X (n - 1), ((M).map (c.ι.app j)).f n w = ((M).obj c.pt).d (n - 1) n y) → ∃ (k : J) (f : j ⟶ k) (y : ((M).obj (D.obj k)).X (n - 1)), ((M).map (D.map f)).f n w = ((M).obj (D.obj k)).d (n - 1) n y) := by
  intro M F0 ι hF0 hι hneg hloc hdesc
  obtain ⟨N, ε, hN, hiso⟩ := GlobalTheory.T.exists_preservesFilteredColimits_iso_on_finiteType AbCx M
  have hterm := (GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN).1
  have hcontN := (GlobalTheory.T.complexCohomology_commutes_with_filteredColimits N hN).2
  haveI : EtFF.IsStableUnderComposition := GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties.1.1.toIsStableUnderComposition

  have hNneg : ∀ n : ℤ, n < 0 → ∀ A, IsZero ((N.obj A).X n) := by
    intro n hn A
    obtain ⟨J, _, _, D, ιA, ⟨hc⟩, hft⟩ := GlobalTheory.T.exists_filteredColimit_finiteType_int_rings A
    have hel := ((GlobalTheory.T.preservesFilteredColimits_addCommGrp_iff_elements CommRingCat.{0} (term N n)).1 (hterm n)) J D _ hc
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    constructor
    intro x y
    suffices h : ∀ x : (N.obj A).X n, x = 0 by rw [h x, h y]
    intro x
    obtain ⟨j, w, rfl⟩ := hel.1 x
    have hz : IsZero ((N.obj (D.obj j)).X n) := by
      haveI := hiso (D.obj j) (hft j)
      have e : (N.obj (D.obj j)).X n ≅ (M.obj (D.obj j)).X n :=
        (HomologicalComplex.eval _ _ n).mapIso (asIso (ε.app (D.obj j)))
      exact (hneg n hn (D.obj j)).of_iso e
    have : w = 0 := by
      rw [AddCommGrpCat.isZero_iff_subsingleton] at hz
      exact @Subsingleton.elim _ hz _ _
    subst this
    exact map_zero _
  have hqis := GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent CommRingCat.{0} EtFF N M ε
    ⟨0, fun n hn U => ⟨hNneg n hn U, hneg n hn U⟩⟩
    (GlobalTheory.T.coveringsRefine_of_cechConerve_property CommRingCat.{0} EtFF _ (fun A B g hg n =>
      ⟨GlobalTheory.T.coalternatingExact_of_finiteType_iso_filteredColimits (term N n) (term M n) (Functor.whiskerRight ε (HomologicalComplex.eval _ _ n)) (hterm n)
        (fun A' hA' => by
          haveI := hiso A' hA'
          change IsIso ((HomologicalComplex.eval _ _ n).map (ε.app A'))
          infer_instance)
        (fun A' B' g' hg' => hdesc A' B' g' hg' n) A B g hg,
       hdesc A B g hg n⟩))
    (GlobalTheory.T.locallySurjective_of_iso_on_finiteType_approximation N M ε F0 ι hF0 hι hneg hloc hN hiso)
    (GlobalTheory.T.locallyInjective_of_iso_on_finiteType_rings N M ε F0 ι hF0 hι hneg hloc hN hiso)
  exact GlobalTheory.T.filteredColimitCohomology_transport_quasiIso N M ε hqis hcontN

end GlobalTheory.EtC.ContAlg
