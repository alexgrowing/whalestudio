import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafPresheafOverCoproductEqSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyLevelwiseCoproductBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.BcCoprod

theorem bc_map_fst {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    (bc p).map g ≫ (pullback.fst p (sch.map U.hom) : (bc p).obj U ⟶ E) = pullback.fst p (sch.map V.hom) := by
  simp only [bc, pullback.map]
  exact pullback.lift_fst _ _ _

theorem bc_map_snd {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    (bc p).map g ≫ (pullback.snd p (sch.map U.hom) : (bc p).obj U ⟶ _) = pullback.snd p (sch.map V.hom) ≫ sch.map g.left := by
  simp only [bc, pullback.map]
  exact pullback.lift_snd _ _ _

theorem isPullback_bc {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    IsPullback ((bc p).map g) (pullback.snd p (sch.map V.hom)) (pullback.snd p (sch.map U.hom)) (sch.map g.left) := by
  have h2 : sch.map g.left ≫ sch.map U.hom = sch.map V.hom := by
    rw [← sch.map_comp, Over.w g]
  have outer : IsPullback ((bc p).map g ≫ (pullback.fst p (sch.map U.hom) : (bc p).obj U ⟶ E))
      (pullback.snd p (sch.map V.hom)) p (sch.map g.left ≫ sch.map U.hom) := by
    rw [bc_map_fst p g, h2]
    exact IsPullback.of_hasPullback p (sch.map V.hom)
  exact IsPullback.of_right outer (bc_map_snd p g) (IsPullback.of_hasPullback p (sch.map U.hom))

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (U : Over S) (ι : Type) (V : ι → Over S) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U.left (fun i => (j i).left)) → ∀ n : ℤ, Function.Bijective (fun (x : H R ((bc p).obj U) F n) (i : ι) => pull R ((bc p).map (j i)) F n x) := by
  intro R _ F S E p U ι V j hc n
  refine GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective R F ((bc p).obj U) ι (fun i => (bc p).obj (V i)) (fun i => (bc p).map (j i)) (fun k => ?_) n
  refine GlobalTheory.T.freeEtaleSheaf_presheaf_over_coproduct_eq_sum R U.left ι (fun i => (V i).left) (fun i => (j i).left) hc (((bc p).obj U).obj k)
    ((pullback.snd p (sch.map U.hom)).app k) (fun i => ((bc p).obj (V i)).obj k)
    (fun i => ((bc p).map (j i)).app k) (fun i => (pullback.snd p (sch.map (V i).hom)).app k) (fun i => ?_)
  exact (isPullback_bc p (j i)).map ((evaluation _ _).obj k)

end GlobalTheory.EtC.BcCoprod
