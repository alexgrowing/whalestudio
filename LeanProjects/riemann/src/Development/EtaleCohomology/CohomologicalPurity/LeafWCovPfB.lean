import Development.EtaleCohomology.CohomologicalPurity.LeafWCovPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

def LeafPLoc : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), LocCov f g →
  ∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0}
    (biprod.desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))

theorem LeafCovLoc_of (hP : LeafPLoc) : LeafCovLoc := by
  intro R _ U V E f g hf hg hL
  refine ⟨hf, hg, fun n => ?_⟩
  let S := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  let a := (freeP R).map (f.app n)
  let b := (freeP R).map (g.app n)
  have h1 : Epi (S.map (biprod.desc a b)) := by
    have : Sheaf.IsLocallySurjective (S.map (biprod.desc a b)) :=
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).2 (hP R f g hL n)
    infer_instance
  change Epi (biprod.desc (S.map a) (S.map b))
  let P := (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)
  let k : S.obj P ⟶ S.obj ((freeP R).obj (U.obj n)) ⊞ S.obj ((freeP R).obj (V.obj n)) :=
    biprod.lift (S.map (biprod.fst : P ⟶ _)) (S.map (biprod.snd : P ⟶ _))
  have h2 : k ≫ biprod.desc (S.map a) (S.map b) = S.map (biprod.desc a b) := by
    simp only [k]
    rw [biprod.lift_desc, ← S.map_comp, ← S.map_comp, ← S.map_add, biprod.desc_eq]
  rw [← h2] at h1
  exact epi_of_epi k _

theorem LeafWCov_of' (hG : LeafGeo) (hP : LeafPLoc) (hW : LeafWLoc) : LeafWCov :=
  LeafWCov_of hG (LeafCovLoc_of hP) hW

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
