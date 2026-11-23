import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambda
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.AmpleForm

theorem relAmple_of_lam_eq : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
    ∀ (M L : LB B.left) (hM : M.IsLB) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L →
    lam (cls M hM) (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) → Out.RelAmple B M := by
  intro K _ _ B _ hB M L hM hL ha hk hlam
  have := hB.comm
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (cls M hM - cls L hL)
  have hlam0 : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, PrimitiveOverField.lam_sub, hlam, sub_self]
  obtain ⟨x, hx⟩ := GlobalTheory.PointTranslate.exists_point_cls_eq_lam K B hB L hL hk O hO hlam0
  have hN : (RigidTranslate.rigTransl L x).IsLB := DVR.linComb_isLB _ hL _ _
  have hA := RigidTranslate.relAmple_rigTransl_point K B hB L hL x ha
  have e1 := PrimitiveOverField.lam_const (cls L hL) x (𝟙 B)
  have e2 : ((toUnit B ≫ x) * 𝟙 B) = PolTranslate.transl x := by
    rw [PolTranslate.transl, _root_.mul_comm]
  have e3 : CechPic.pull (toUnit B ≫ x).left (cls L hL) = 0 := by
    rw [Over.comp_left, CechPic.pull_comp, ThetaExtend.pic_local (CechPic.pull x.left (cls L hL)), map_zero]
  have e : cls M hM = cls _ hN := by
    rw [CechPic.cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, e3, neg_zero, add_zero]
    rw [e2, Over.id_left, CechPic.pull_id] at e1
    exact sub_left_inj.1 (eO.symm.trans (hx.trans e1))
  have hN' := pull_isLB hN (𝟙 _)
  have e' : cls M hM = cls _ hN' := by
    rw [CechPic.cls_pull hN, CechPic.pull_id]; exact e
  obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hM hN').1 e'
  exact relAmple_pull (A' := B) (A := B) (φ := 𝟙 _) (f := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩) hN hM ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) hA

end GlobalTheory.CompanionTheory.AmpleForm
