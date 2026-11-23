import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle
import Formalism.LocalToGlobal.ProjectiveLattices.TensPtsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Vert GlobalTheory.LocM
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LocM

open ReciprocityTheory.ChartRestriction.G.Out (RosatiAdj rosatiφ rosatiε)
open GlobalTheory.CechPic

theorem abPartAct_isAdj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (t : SAB H (Sp R)) (U : PELUnif I t) :
    GlobalTheory.HermTensor.IsAdj (abPartAct U) U.D.toPre.P.L := by
  intro c
  have hr : RosatiAdj U.D.toPre.P.A U.D.toPre.P.L ((abPartAct U).act c) ((abPartAct U).act (star c)) := by
    have h : RosatiAdj U.D.toPre.P.A U.D.toPre.P.L ((abPartAct U).act c) ((abPartAct U).act (H.bar c)) := by
      letI := H.starRing
      exact U.oD.onB.rosati c
    rw [← bar_eq_star H]
    exact h
  obtain ⟨V, hV, g, hg⟩ := hr (IsLocalRing.closedPoint R)
  obtain rfl : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hV
  have hL : U.D.toPre.P.L.IsLB := U.D.toPre.P.isLB
  have hgen : ∃ u : LB.Gen (LB.LinComb U.D.toPre.P.L
      (rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c))) rosatiε), u.IsGen := by
    have e : rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c)) = fun i =>
        (U.D.toPre.P.A ⊗ U.D.toPre.P.A).left.topIso.inv ≫ ((U.D.toPre.P.A ⊗ U.D.toPre.P.A).hom ⁻¹ᵁ ⊤).ι ≫
          rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c)) i :=
      funext fun i => ((U.D.toPre.P.A ⊗ U.D.toPre.P.A).left.topIso.inv_hom_id_assoc _).symm
    rw [e]
    exact ⟨_, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hg _⟩
  obtain ⟨u, hu⟩ := hgen
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨u, hu⟩
  rw [cls_linComb hL, Fin.sum_univ_six] at h0
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1 ?_
  refine (cls_cube_two hL _ _ _).trans (Eq.trans ?_ (cls_cube_two hL _ _ _).symm)
  have pm : ∀ a b : U.D.toPre.P.A ⊗ U.D.toPre.P.A ⟶ U.D.toPre.P.A, padd U.D.toPre.P.A a b = a * b := fun _ _ => rfl
  simp only [rosatiφ, rosatiε, lam, pm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons,
    one_smul, neg_smul, Fin.isValue] at h0 ⊢
  rw [← sub_eq_zero, ← h0]
  abel

end GlobalTheory.LocM
