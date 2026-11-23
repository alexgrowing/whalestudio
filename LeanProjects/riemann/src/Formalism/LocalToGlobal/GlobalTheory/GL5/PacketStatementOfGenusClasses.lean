import Formalism.LocalToGlobal.GlobalTheory.ConcTop
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassItems
import Formalism.LocalToGlobal.GlobalTheory.GL5.LocalEndomorphismContinuous
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountRec

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.ConcTop

def RowRec (𝒞 : FamClass) (P : D7 → Prop) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x (i : Fm.Ix x), P (Fm.D x i)

def RowCount (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => FamilyMassVolumeBounds Fm → FamilyLevelConditionAdmitted Fm →
    ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev

def RowClsTie (𝒞 : FamClass) : Prop :=
  Closed 𝒞 fun Fm _ => ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Nonempty (Formalism.MainNotions.Gaps.CC.ClsTie (Fm.D x i))

section LH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem landherrHasse_of_sig (D : D7) (hL : LandherrSig D) : LandherrHasse D := by
  intro W hW hsig
  obtain ⟨φ, hφ⟩ := hL (stdPos D W.rank) W (stdPos_sigOK D W.rank) hW (stdPos_rank D W.rank)
    (fun τ => by rw [stdPos_sig, hsig])
  refine ⟨fun a => φ ((stdPos D W.rank).frame a), ?_, fun a c => ?_⟩
  · exact (stdPos D W.rank).frame.linearIndependent.map' φ.toLinearMap φ.ker
  · rw [hφ]
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (fun x hx => Formalism.BasicNotions.Examples₂.star_isIntegral x hx) W.rank
      (fun _ => false) W.rank 0 a c).trans ?_
    simp [Formalism.BasicNotions.Examples₂.sgn]

end LH

theorem classItemsAt_all (D : D7) (hG : GenusMassStd D) (hM : ClassMass D) (n : ℕ) : ClassItemsAt D n :=
  ⟨genusMassAt_of D hG n, class_number_finite_rank D n, classMassAt_of D hM n⟩

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem stmtF_of_named {eps : ℝ} (Fm : FamP eps) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : ∀ x (i : Fm.Ix x), Formalism.L2.Theta.RealTied (Fm.D x i))
    (hW : WeilSiegelCM)
    (hV : ∀ x (i : Fm.Ix x), VolSigIndep (Fm.D x i))
    (hM : ∀ x (i : Fm.Ix x), ClassMass (Fm.D x i))
    (hHC : ∀ x (i : Fm.Ix x), HCFormalDegree (Fm.D x i))
    (hL : ∀ x (i : Fm.Ix x), LandherrSig (Fm.D x i))
    (hG : ∀ x (i : Fm.Ix x), GenusMassStd (Fm.D x i))
    (hN : FamilyMassVolumeBounds Fm → FamilyLevelConditionAdmitted Fm → ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev) :
    KudlaFamilyStatement Fm C3 :=
  stmtF_of_open Fm C3 (by linarith) (siegel_weil_part_one_of_weil_theorem eps Fm hW)
    (fun _ => standardMassRatio_of_modelMassRatio Formalism.HermitianLattices.SiegelMassBounds.siegel_mass_ratio)
    (fun _ hT x i => ⟨theorem_two_of_landherr (Fm.D x i) (hT x i) (hV x i) (hL x i)
        (fun n _ => classItemsAt_all (Fm.D x i) (hG x i) (hM x i) n),
      volume_mass_of_class_items (Fm.D x i) (hT x i) (hG x i) (class_number_finite (Fm.D x i)) (hM x i)⟩)
    (fun hA x i => theorem_three_all_unitary (Fm.D x i) C3 hC3 (hR x i).cdScale (hHC x i) (hA x i).2.2)
    (fun x hx i => levels_pro_g (Fm.D x i) (Fm.ex x hx i).lev)
    hN
    (fun x i => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.landherrSmall_of_hasse (Fm.D x i) (landherrHasse_of_sig (Fm.D x i) (hL x i)))

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem packet_statement_of_named (𝒞 : FamClass) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : RowReal 𝒞)
    (hW : WeilSiegelCM)
    (hV : RowRec 𝒞 VolSigIndep)
    (hM : RowRec 𝒞 ClassMass)
    (hHC : RowRec 𝒞 HCFormalDegree)
    (hL : RowRec 𝒞 LandherrSig)
    (hG : RowRec 𝒞 GenusMassStd)
    (hN : RowCount 𝒞) : ClosedKudlaFamilyStandardLattice 𝒞 C3 :=
  (((((hR.and hV).and hM).and hHC).and hL).and (hG.and hN)).imp
    fun Fm _ _ h => stmtF_of_named Fm C3 hC3 h.1.1.1.1.1 hW h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 h.1.2 h.2.1 h.2.2

theorem rowRec_of_all {𝒞 : FamClass} {P : D7 → Prop} (hP : ∀ D, P D) (hR : RowReal 𝒞) : RowRec 𝒞 P :=
  hR.imp fun Fm _ _ _ x i => hP (Fm.D x i)

theorem rowCount_of_clsTie {𝒞 : FamClass} (h : RowClsTie 𝒞) : RowCount 𝒞 :=
  h.imp fun Fm _ _ h _ _ x hx i => (h x hx i).elim fun X => Formalism.MainNotions.Gaps.CC.class_number_of_class_data X (Fm.ex x hx i).lev

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem packet_statement_of_genus_classes (𝒞 : FamClass) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : RowReal 𝒞) (hW : WeilSiegelCM) (hV : RowRec 𝒞 VolSigIndep)
    (hUJ : PI.UJClassMass2.UJClassMass)
    (hHC : RowRec 𝒞 HCFormalDegree) (hL : RowRec 𝒞 LandherrSig)
    (hG : RowRec 𝒞 GenusMassStd) (hX : RowClsTie 𝒞) : ClosedKudlaFamilyStandardLattice 𝒞 C3 :=
  packet_statement_of_named 𝒞 C3 hC3 hR hW hV (rowRec_of_all (class_mass_of_genus_classes hUJ) hR) hHC hL hG (rowCount_of_clsTie hX)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem packet_statement_of_surjection (𝒞 : FamClass) (C3 : ℝ) (hC3 : 1 ≤ C3)
    (hR : RowReal 𝒞) (hW : WeilSiegelCM) (hV : RowRec 𝒞 VolSigIndep)
    (hLG : ClassSteps.LatGenus) (hSS : PI.UnitaryGroupMassFormula.UJClassMass.SurjStep)
    (hHC : RowRec 𝒞 HCFormalDegree) (hL : RowRec 𝒞 LandherrSig)
    (hG : RowRec 𝒞 GenusMassStd) (hX : RowClsTie 𝒞) : ClosedKudlaFamilyStandardLattice 𝒞 C3 :=
  packet_statement_of_named 𝒞 C3 hC3 hR hW hV (rowRec_of_all (classMass_of_steps hLG hSS) hR) hHC hL hG (rowCount_of_clsTie hX)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

end
