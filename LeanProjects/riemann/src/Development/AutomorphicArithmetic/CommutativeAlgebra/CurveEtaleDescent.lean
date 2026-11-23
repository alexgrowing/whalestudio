import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.CommutativeAlgebra.CechDescentTwistOfProperSurjectiveStrictlyHensel
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EquivOfStalkwiseBaseChange
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistFinitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

private theorem qcqs_id (X : Scheme.{0}) : QcqsOver (𝟙 (sch.obj X)) := by
  intro k
  refine ⟨X, 𝟙 X, Iso.refl _, inferInstance, inferInstance, ?_⟩
  simp
  exact Category.id_comp _

private theorem qcqs_cech {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] :
    QcqsOver (cechAug f ≫ 𝟙 (sch.obj X)) := by
  intro k
  obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsProper Y X f inferInstance k
  haveI := hπ
  refine ⟨Z, π ≫ f, e, inferInstance, inferInstance, ?_⟩
  simpa using he

private theorem stalk_eqv (R : Type) [CommRing R] (F : Shv R) {Y X T : Scheme.{0}} (f : Y ⟶ X) (s : T ⟶ X)
    (h : Eqv R (cechAug (pullback.snd f s)) F) :
    Eqv R ((bcMap (cechAug f) (𝟙 (sch.obj X))).app (Over.mk s)) F := by
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  obtain ⟨m, hpb, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback Y X (pullback f s) T (pullback.fst f s) (pullback.snd f s) f s
    (IsPullback.of_hasPullback f s)
  have hpb' : IsPullback m (cechAug (pullback.snd f s)) (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s) := by
    rw [Category.comp_id]
    exact hpb
  let g : pullback (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s) ⟶ pullback (𝟙 (sch.obj X)) (sch.map s) :=
    (bcMap (cechAug f) (𝟙 (sch.obj X))).app (Over.mk s)
  have hsnd : g ≫ pullback.snd (𝟙 (sch.obj X)) (sch.map s)
      = pullback.snd (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s) := by
    dsimp only [g, bcMap]
    erw [pullback.lift_snd]
    exact Category.comp_id _
  have hQ : Eqv R (pullback.snd (𝟙 (sch.obj X)) (sch.map s)) F := hiso _ _ _ inferInstance
  have hι : Eqv R hpb'.isoPullback.hom F := hiso _ _ _ inferInstance
  have key : (hpb'.isoPullback.hom ≫ g) ≫ pullback.snd (𝟙 (sch.obj X)) (sch.map s)
      = cechAug (pullback.snd f s) := by
    rw [Category.assoc, hsnd, hpb'.isoPullback_hom_snd]
  have h1 : Eqv R (hpb'.isoPullback.hom ≫ g) F := by
    refine (hcomp _ _ _ _ _).2.2 hQ ?_
    rw [key]
    exact h
  exact ((hcomp _ _ _ _ _).2.1 hι h1 : Eqv R g F)

theorem UpperTheory.curve_etale_descent :
    LateralTheory.E.E4.LeafDesc := by
  intro hH q _ k _ hq Y X p _ f _ _ i
  refine UpperTheory.Cb.equiv_of_stalkwise_base_change (ZMod q) (tw q i) X _ _ (cechAug f) (𝟙 (sch.obj X)) (UpperTheory.Cb.tateTwist_finitary q i)
    (qcqs_cech f) (qcqs_id X) ?_
  intro O _ s hs
  apply stalk_eqv
  have hqO : IsUnit ((q : ℕ) : O) := by
    have φ := Spec.preimage (s ≫ p)
    simpa using hq.map φ.hom
  exact UpperTheory.cech_descent_twist_of_proper_surjective_strictly_henselian hH q O hs.1 hqO (pullback.snd f s) i
