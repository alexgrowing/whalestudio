import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineHomOfIsAffineHomPullbackSndOfFpqc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialise

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem torus_isAffineHom_and_splits_finite : NaSt.{0} := by
  intro k _ T _ hT
  obtain ⟨Ω, _, _, X, _, _, _, e, he⟩ := hT.splits
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    ⟨fun x => ⟨(default : Spec (.of Ω)), Subsingleton.elim (α := Spec (.of k)) _ _⟩⟩
  have haff : IsAffineHom T.hom := by
    refine isAffineHom_of_isAffineHom_pullback_snd_of_fpqc _ _ _ T.hom _ hsurj hflat inferInstance ?_
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have h : IsAffineHom (e.hom.left ≫ (splitTorus (Spec (.of Ω)) X).hom) := inferInstance
    rw [Over.w] at h
    exact h
  refine ⟨haff, ?_⟩
  obtain ⟨k', _, _, _, e', he'⟩ := IsoFinite.exists_finite_iso k Ω T (splitTorus (Spec (.of k)) X)
    haff inferInstance hT.finiteType inferInstance
    ⟨e ≪≫ (Diag.baseChangeIso _ X).symm,
      inferInstanceAs (IsMonHom (e.hom ≫ (Diag.baseChangeIso _ X).inv))⟩
  exact ⟨k', inferInstance, inferInstance, inferInstance, X, inferInstance, inferInstance, inferInstance,
    e' ≪≫ Diag.baseChangeIso _ X, inferInstanceAs (IsMonHom (e'.hom ≫ (Diag.baseChangeIso _ X).hom))⟩

end GlobalTheory
