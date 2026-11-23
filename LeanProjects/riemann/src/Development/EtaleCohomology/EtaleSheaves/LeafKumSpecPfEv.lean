import Development.EtaleCohomology.EtaleSheaves.LeafKumSpecPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafKumSpecPf

theorem freeGen_res (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  have := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
    (ModuleCat.freeMk (ULift.up x))
  have hm : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up ((P.map g.op) x)) := by
    simp [freeP, ModuleCat.freeMk]
    first | (rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl) | (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl) | (simp [Finsupp.mapDomain_single]; rfl)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hm] at this
  exact this.symm

end LateralTheory.E.LeafKumSpecPf
