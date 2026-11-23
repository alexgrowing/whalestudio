import Development.AutomorphicArithmetic.CommutativeAlgebra.TateTwistAffineLineProjectionEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankOneOfHomotopyInvarian
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankTwo
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfMayerVietorisCover
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingExistsUniqueAdditiveExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.FirstChernClassEqZeroOfIsTrivialized
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal
import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyExistsIsUnitOfSpanRangeEqTop
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductMapOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductPairOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.StackProductIsPullbackOfActionPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfIsoSquare
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOneIffTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineActionFstTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisStackProductOfInjectiveOfLocallyCov
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjBundleFormulaIffPglForm
import Development.AutomorphicArithmetic.CommutativeAlgebra.LeraHirschOfLocalCoverOfInf
import Development.AutomorphicArithmetic.CommutativeAlgebra.LeraHirschChernPowersOnUnitChart
import Development.AutomorphicArithmetic.CommutativeAlgebra.LeraHirschUnitOnBlowupChart
import Development.AutomorphicArithmetic.CommutativeAlgebra.EqvTwistUnimodularUnitLocus
import Development.AutomorphicArithmetic.CommutativeAlgebra.EqvTwistBlowupRestriction
import Development.AutomorphicArithmetic.CommutativeAlgebra.ChernClassPullbackBlowupFirstLocusEqZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.ChernClassPullbackBlowupSecondLocusEq
import Development.AutomorphicArithmetic.CommutativeAlgebra.TwoOpenCoverOfMapIncl
import Development.AutomorphicArithmetic.CommutativeAlgebra.TwoOpenCoverOfMapInclComap
import Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyLiftOfLiftOnUnitCubeFaces
import Development.AutomorphicArithmetic.CommutativeAlgebra.PullbackCubeFacesEquivTateTwist
import Development.AutomorphicArithmetic.CommutativeAlgebra.CpowSuccEqCupOfTwoCover
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfPullbackSquare
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfTwoCoversPullbackSquare
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.projectiveBundleFormula_succ_of_forall :
    ∀ (q : ℕ) [NeZero q] (N : ℕ), 2 ≤ N → (∀ E : Spc, Inv q E → PBF q E N) → ∀ E : Spc, Inv q E → PBF q E (N + 1) := by
  intro q _ N hN H E hE
  have hN1 : 1 ≤ N := by omega
  have invS : ∀ (a : Act), Inv q (Sp E a) := fun a U ⟨x⟩ => hE U ⟨x.1⟩
  refine (UpperTheory.projBundleFormula_iff_pglForm q E (N + 1) hE).2 ?_
  have hX : Pbf q E N := (UpperTheory.projBundleFormula_iff_pglForm q E N hE).1 (H E hE)
  have hc : Sp.map E (βC N) ≫ Sp.line E (chiX (N + 1)) = Sp.line E (chiB N) := rfl
  have hξ : pull _ (Sp.map E (βC N)) _ _ (c1 q (Sp.line E (chiX (N + 1)))) = c1 q (Sp.line E (chiB N)) := by
    rw [(GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ (invS _), hc]
  have hh : pull _ (Sp.map E (pC N)) _ _ (c1 q (Sp.line E (chiX N))) = c1 q (Sp.line E (chiH N)) := by
    rw [(GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ (invS _)]
    rfl
  have hlh : LH q (Sp.map E (pC N)) (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ))
      (fun j => cpow q (pull _ (Sp.map E (βC N)) _ _ (c1 q (Sp.line E (chiX (N + 1))))) j) := by
    rw [hξ]
    exact UpperTheory.cohomology_lift_of_lift_on_unit_cube_faces q N E hN1 hE (pC N) _ _ _ (fun i Q hQ => UpperTheory.leraHirsch_chernPowers_on_unitChart q N E i Q hQ hE)
  have hB1 : ∀ i, Eqv _ (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.map E (pC N)) (tw q i) := fun i =>
    (UpperTheory.lerayHirsch_one_iff_twist_equiv q (Sp.map E ((incl ((Q1 N).comap (βC N))).comp (pC N))) (invS _)).1
      (UpperTheory.cohomology_lift_of_lift_on_unit_cube_faces q N E hN1 hE _ _ _ _ (fun i Q hQ => UpperTheory.leraHirsch_unit_on_blowupChart q N E i Q hQ hE)) i
  have r1 : pull _ (Sp.map E (incl ((Q1 N).comap (βC N)))) _ _ (pull _ (Sp.map E (βC N)) _ _ (c1 q (Sp.line E (chiX (N + 1))))) = 0 := by
    rw [hξ]
    exact UpperTheory.chernClass_pullback_blowupFirstLocus_eq_zero q N E hE
  have r2 : pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (pull _ (Sp.map E (βC N)) _ _ (c1 q (Sp.line E (chiX (N + 1))))) =
      pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (pull _ (Sp.map E (pC N)) _ _ (c1 q (Sp.line E (chiX N)))) := by
    rw [hξ, hh]
    exact UpperTheory.chernClass_pullback_blowupSecondLocus_eq q N E hE
  have rel := UpperTheory.cpow_succ_eq_cup_of_two_cover q (Sp.map E (incl ((Q1 N).comap (βC N)))) (Sp.map E (incl ((Q2 N).comap (βC N))))
    (pull _ (Sp.map E (βC N)) _ _ (c1 q (Sp.line E (chiX (N + 1))))) (pull _ (Sp.map E (pC N)) _ _ (c1 q (Sp.line E (chiX N))))
    (invS _) (UpperTheory.two_open_cover_of_map_incl_comap _ N E) r1 r2
  intro n i
  refine ⟨UpperTheory.leray_hirsch_of_pullback_square q N hN1 (Sp.fst E (XC N)) (Sp.fst E (XC (N + 1))) (Sp.map E (pC N)) (Sp.map E (βC N)) rfl
      (c1 q (Sp.line E (chiX N))) (c1 q (Sp.line E (chiX (N + 1)))) (invS _) (invS _) hX hlh rel n i,
    UpperTheory.leray_hirsch_of_two_covers_pullback_square q N hN1 (Sp.fst E (XC N)) (Sp.fst E (XC (N + 1))) (Sp.map E (pC N)) (Sp.map E (βC N))
      (Sp.map E (incl (Q1 N))) (Sp.map E (incl (Q2 N))) (Sp.map E (incl ((Q1 N).comap (βC N))))
      (Sp.map E (incl ((Q2 N).comap (βC N)))) (Sp.map E ((βC N).sub (Q1 N))) (Sp.map E ((βC N).sub (Q2 N)))
      rfl rfl rfl (c1 q (Sp.line E (chiX N))) (c1 q (Sp.line E (chiX (N + 1)))) (invS _) (invS _) (invS _)
      (UpperTheory.two_open_cover_of_map_incl _ N E) (UpperTheory.two_open_cover_of_map_incl_comap _ N E) hX hlh (fun i => UpperTheory.eqv_twist_unimodularUnitLocus q N E i hE) hB1
      (fun i => UpperTheory.eqv_twist_blowupRestriction q N E (Q2 N) i (fun _ _ h => h) hE) (fun i => UpperTheory.pullback_cube_faces_equiv_tate_twist q N E i _ _ hE) r1 rel n i⟩
