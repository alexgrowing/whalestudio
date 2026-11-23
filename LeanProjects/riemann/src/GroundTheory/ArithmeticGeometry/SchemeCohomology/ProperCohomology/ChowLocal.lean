import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A : Type u} [CommRing A]

abbrev chartStructureMap (n : ℕ) : A →+* Chart A (0 : Fin (n + 1)) :=
  (fromZeroRingHom (grading A n) _).comp (algebraMap A (grading A n 0))

lemma chartToPoly_chartStructureMap (n : ℕ) (a : A) :
    chartToPoly A (0 : Fin (n + 1)) (chartStructureMap n a) = C a := by
  have h : chartStructureMap (A := A) n a = polyToChart A 0 (C a) := by
    simp [polyToChart]
  rw [h, ← RingHom.comp_apply, chartToPoly_polyToChart, RingHom.id_apply]

theorem exists_surjective_chart {B : Type u} [CommRing B] (ρ : A →+* B) (hρ : ρ.FiniteType) :
    ∃ (n : ℕ) (g : Chart A (0 : Fin (n + 1)) →+* B), Function.Surjective g ∧
      g.comp (chartStructureMap n) = ρ := by
  let _ := ρ.toAlgebra
  obtain ⟨n, s, hs⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hρ
  let ψ : MvPolynomial {j : Fin (n + 1) // j ≠ 0} A →+* B :=
    eval₂Hom ρ fun j => s (X (j.1.pred j.2))
  let e : Fin n → {j : Fin (n + 1) // j ≠ 0} := fun k => ⟨k.succ, Fin.succ_ne_zero k⟩
  have hψ : ∀ p, ψ (rename e p) = s p := by
    intro p
    rw [MvPolynomial.aeval_unique s]
    simp only [ψ, coe_eval₂Hom, eval₂_rename, e, aeval_def]
    rfl
  refine ⟨n, ψ.comp (chartToPoly A 0), ?_, ?_⟩
  · intro b
    obtain ⟨p, rfl⟩ := hs b
    obtain ⟨z, hz⟩ := (chartEquiv A (0 : Fin (n + 1))).surjective (rename e p)
    exact ⟨z, by rw [RingHom.comp_apply]; change ψ (chartEquiv A 0 z) = _; rw [hz, hψ]⟩
  · ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, chartToPoly_chartStructureMap]
    simp [ψ]

theorem exists_closedImmersion_stdOpen {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (c : U.toScheme ⟶ (stdOpen A n 0).toScheme), IsClosedImmersion c ∧
      c ≫ (stdOpen A n 0).ι ≫ toSpecBase A n = U.ι ≫ f := by
  let ρ' : CommRingCat.of A ⟶ Γ(X, U) := (Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U le_top
  have hρ : ρ'.hom.FiniteType := by
    refine RingHom.FiniteType.comp (f.finiteType_appLE (isAffineOpen_top _) hU le_top) ?_
    exact RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2
  obtain ⟨n, g, hg, hgc⟩ := exists_surjective_chart ρ'.hom hρ
  have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) A) ∈ grading A n 1 := X_mem 0
  let c : U.toScheme ⟶ (Proj.basicOpen (grading A n) (MvPolynomial.X 0)).toScheme :=
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g) ≫
      (Proj.basicOpenIsoSpec (grading A n) (MvPolynomial.X 0) hX0 one_pos).inv
  have hc : IsClosedImmersion c := by
    have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg
    dsimp only [c]
    infer_instance
  refine ⟨n, c, hc, ?_⟩
  have h1 : U.ι ≫ f = hU.isoSpec.hom ≫ Spec.map ρ' := by
    rw [← hU.isoSpec_hom_fromSpec, Category.assoc,
      ← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec, asIso_inv]
    congr 1
    rw [IsIso.comp_inv_eq, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    congr 1
    simp [ρ']
  rw [h1]
  change hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g) ≫
      ((Proj.basicOpenIsoSpec (grading A n) (MvPolynomial.X 0) hX0 one_pos).inv ≫
        (Proj.basicOpen (grading A n) (MvPolynomial.X 0)).ι) ≫ toSpecBase A n = _
  rw [Proj.basicOpenIsoSpec_inv_ι, toSpecBase, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext a
  change g (chartStructureMap n a) = ρ'.hom a
  rw [← RingHom.comp_apply, hgc]

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
