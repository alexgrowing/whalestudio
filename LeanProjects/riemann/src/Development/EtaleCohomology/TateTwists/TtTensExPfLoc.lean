import Development.EtaleCohomology.TateTwists.TtTensExPf

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

theorem tt_sheafify_locSurj (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : ((presheafToSheaf Scheme.etaleTopology.{0} _).obj P).obj.obj (op U)) :
    Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology.{0} P).app (op V)).hom x =
      (((presheafToSheaf Scheme.etaleTopology.{0} _).obj P).obj.map g.op).hom y :=
  ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} P) y,
    fun _ _ ⟨x, hx⟩ => ⟨x, hx⟩⟩

theorem tt_sheafify_locInj (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (x : P.obj (op U)) (hx : ((toSheafify Scheme.etaleTopology.{0} P).app (op U)).hom x = 0) :
    Loc U fun _ g => (P.map g.op).hom x = 0 := by
  refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} P) x 0
    (by simpa using hx), fun _ _ h => ?_⟩
  simpa using h

end LateralTheory.EtaleFoundations
