import Development.EtaleCohomology.EtaleDuality.PointClasses

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite CochainComplex.HomComplex
namespace LateralTheory.EDual

theorem sec_empty_sub {R : Type} [CommRing R] (G : Shv R) (U : Scheme.{0}) [IsEmpty U] :
    Subsingleton (G.obj.obj (op U)) := by
  have hS := (G.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R))) (⊥ : Sieve U)
    (Scheme.bot_mem_grothendieckTopology U)
  refine ⟨fun x y => ?_⟩
  have e := hS.isSeparatedFor (fun _ _ h => h.elim) (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)) (fun _ _ h => h.elim) (fun _ _ h => h.elim)
  have := congrArg (fun φ => φ.hom (1 : ULift.{1} R)) e
  simpa using this

end LateralTheory.EDual
