import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionDegenerationLinearUniformisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsSymmetricFrameAndTerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
namespace GlobalTheory.UT.ClModel

theorem galois_all : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Galois U := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ F' _ _ _ σ k hk p
  refine ⟨qkExtExists R D.toPre F F' σ.toRingHom (fun r => σ.commutes r) k p, fun x => ?_, fun p' x x' h h' =>
    GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt GlobalTheory.firstFiveLaws R I hI D A G hG U F F' σ k hk p p' x x' h h'⟩
  refine ⟨Over.homMk (spMap σ.toRingHom ≫ x.left) ?_, rfl⟩
  rw [Category.assoc, Over.w x]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  all_goals exact σ.commutes _

theorem functorial_all : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Functorial U := by
  intro R _ _ _ I hI D A G _ _ hG U
  obtain ⟨-, h1, h2, h3, h4⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  refine ⟨GlobalTheory.EndData.exists_endU GlobalTheory.firstFiveLaws R I hI D A G hG U, fun E E' h =>
    ⟨GlobalTheory.UT.rosatiAdj_and_c_linear_of_endU GlobalTheory.firstFiveLaws R I hI D A G hG U E E' h, fun F _ _ _ =>
      ⟨(GlobalTheory.EndCalc.end_calculus GlobalTheory.firstFiveLaws R I hI D A G hG U F E E E).1,
        GlobalTheory.Balanced.main GlobalTheory.firstFiveLaws h1 h2 h3 h4 R I hI D A G hG U F E E' h⟩⟩⟩

theorem familyRing_all : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.FamilyRing U := by
  intro R _ _ _ I hI D A G _ _ hG U
  exact ⟨(GlobalTheory.UT.expBijF_and_expandsF_lin GlobalTheory.firstFiveLaws R I hI D A G hG U).1, fun F _ _ _ =>
    GlobalTheory.UT.ProdConv.main GlobalTheory.firstFiveLaws R I hI D A G hG U F⟩

theorem balanced_all : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Balanced U := by
  intro R _ _ _ I hI D A G _ _ hG U
  obtain ⟨-, h1, h2, h3, h4⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  exact ⟨GlobalTheory.RingActData.exists_oAct GlobalTheory.firstFiveLaws h1 h2 h3 h4 R I hI D A G hG U,
    GlobalTheory.PsiPrim.traceFormTwistIso_of_primitive_lineBundle GlobalTheory.firstFiveLaws h1 h2 h3 h4 R I hI D A G hG U⟩

theorem seriesVal_all (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hV : IsAdicComplete (maximalIdeal V) V) (D : DegData V (maximalIdeal V)) : Cl.SeriesVal D := by
  obtain ⟨-, h1, h2, h3, h4⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  intro ϖ hϖ
  refine ⟨?_, fun Q hQ F _ _ _ v hv => ?_⟩
  · choose Q hQ using QForm.exists_QVal hϖ D
    exact ⟨Q, hQ⟩
  · have h := GlobalTheory.UT.TxVal.main GlobalTheory.firstFiveLaws h1 h2 h3 h4 V hV ϖ hϖ D Q hQ F v hv
    refine ⟨h.1, fun m hm p g' w' hs => ?_⟩
    obtain ⟨hg, hw', w, κ, hw, hκ, e⟩ := hs
    exact (h.2 m hm p w hw g' hg κ hκ w' hw' e).2.2

theorem rank_one_model :
    ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries ℚ))))) (G : Over (Spec (CommRingCat.of (PowerSeries ℚ))))
      (_ : GrpObj G) (_ : IsCommMonObj G) (D : DegData (PowerSeries ℚ) (maximalIdeal (PowerSeries ℚ)))
      (U : Unif (maximalIdeal (PowerSeries ℚ)) D A G), Module.finrank ℤ D.toPre.X = 1 ∧
      Cl.Torsion U ∧ Cl.Galois U ∧ Cl.Functorial U ∧ Cl.FamilyRing U ∧ Cl.Balanced U ∧ Cl.SeriesVal D ∧
      (∃ (p : QkPt D.toPre (AlgebraicClosure (FractionRing (PowerSeries ℚ))) (3 ^ 2)) (x : _) (w : _),
        p.y ≠ 0 ∧ QkToAkU U.toUnifPre _ (3 ^ 2) p x ∧ TXFrame (3 ^ 2) p w) ∧
      ∃ (D' : DegData (PowerSeries ℚ) (maximalIdeal (PowerSeries ℚ))) (A' : PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries ℚ)))))
        (G' : Over (Spec (CommRingCat.of (PowerSeries ℚ)))) (_ : GrpObj G') (_ : IsCommMonObj G'),
        IsSemiAbelian G' ∧ Nonempty (Unif (maximalIdeal (PowerSeries ℚ)) D' A' G') ∧
          Nonempty (IsPullDeg (RingHom.id _) D.toPre D'.toPre) := by
  have hc : IsAdicComplete (maximalIdeal (PowerSeries ℚ)) (PowerSeries ℚ) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have : CharZero (PowerSeries ℚ) := algebraRat.charZero _
  obtain ⟨A, G, _, _, D, U, hG, -, hX, -⟩ := GlobalTheory.TateUnif.exists_unif_rank_one
  have hR : AdmBase (PowerSeries ℚ) (maximalIdeal (PowerSeries ℚ)) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hT := GlobalTheory.TorsionIso.torsion_clause _ _ hR D A G hG U
  refine ⟨A, G, inferInstance, inferInstance, D, U, hX, hT, galois_all _ _ hR D A G hG U, functorial_all _ _ hR D A G hG U,
    familyRing_all _ _ hR D A G hG U, balanced_all _ _ hR D A G hG U, seriesVal_all _ hc D, ?_, ?_⟩
  · have : Nontrivial D.toPre.X := Module.nontrivial_of_finrank_pos (R := ℤ) (by omega)
    obtain ⟨y, hy⟩ := exists_ne (0 : D.toPre.X)
    obtain ⟨h, hh⟩ := GlobalTheory.TorusExt.exists_iota (F := AlgebraicClosure (FractionRing (PowerSeries ℚ))) D.tau_bimult y
    obtain ⟨g, hg⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws _ _ hR D
      (AlgebraicClosure (FractionRing (PowerSeries ℚ)))).2.1 (3 ^ 2) (by norm_num) h
    let p : QkPt D.toPre (AlgebraicClosure (FractionRing (PowerSeries ℚ))) (3 ^ 2) := ⟨y, g, h, hg, hh⟩
    obtain ⟨f, hf, -⟩ := hT (AlgebraicClosure (FractionRing (PowerSeries ℚ))) (3 ^ 2) (by norm_num)
    obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws _ _ hR D
      (AlgebraicClosure (FractionRing (PowerSeries ℚ))) (3 ^ 2) (by decide) p).1
    exact ⟨p, f p, w, hy, (hf.1 p _).2 rfl, hw⟩
  · obtain ⟨D', hD, A', U', hG', -⟩ := GlobalTheory.UT.EndBaseChange.main GlobalTheory.firstFiveLaws _ _ hR D A G hG U (PowerSeries ℚ)
      (RingHom.id _) hc Function.injective_id (by simp)
    exact ⟨D', A', _, inferInstance, inferInstance, hG', ⟨U'⟩, ⟨hD⟩⟩

end GlobalTheory.UT.ClModel
end
