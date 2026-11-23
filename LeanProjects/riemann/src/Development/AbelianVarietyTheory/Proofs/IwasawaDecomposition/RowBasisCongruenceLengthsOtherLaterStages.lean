import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mem.R3.Rw.rr_eta_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m) (R : RealDat3 a.D A3 Ks) (F : Face3 a.D A3), letI := alg b iK; (∀ j v, etaOf (real3 b R) (face3 b F) j v = etaOf R F j ((v))) ∧ ∀ (y : Hd R.toRealDat) (y' : Hd (real3 b R).toRealDat) (bb : Bool) (E : Hs) jE jE' n c Xo, HEq jE' jE → RrT F y bb (E := E) jE n c Xo → RrT (face3 b F) y' bb (E := E) jE' n c ((Xo)) := by
  intro B C a b G _ _ Pl0 I0 T Ks _ _ iK A3 R F
  letI := alg b iK
  refine ⟨fun j v => ?_, fun y y' bb E jE jE' n c Xo hj h => ?_⟩
  · tr_via (fun X : Cx.CxData A3.fam3.amb3 => (open Classical in
        if hj : 1 ≤ j ∧ j ≤ a.D.R.m then
          if a.D.plEq (((v :))) ∈ R.twPl then
            A3.A.fam.etaJ F.P0 F.ψ0 (A3.fam3.toSub2 X.zs) ⟨j - 1, by omega⟩ (R.mu (a.D.plEq (((v :))))) (a.D.plEq (((v :))))
          else 0
        else 0) = etaOf R F j ((by with_unfolding_all exact (v :)))) (toCx3_eq b R F) (Eq.refl (etaOf R F j ((by with_unfolding_all exact (v :)))))
  · have e : jE' = jE := eq_of_heq hj
    subst jE'
    tr_via (fun u : Parts R => ∃ h : n = ((cxW R F u).data F.cr bb).D,
      (∀ x : Fin n → a.D.what₂.LL, jE (∑ i, a.D.what₂.embLL (x i) • c i) =
        PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt a.D.what₂.embLL A3.A.v0) (E := R.HE.H)
          ((by with_unfolding_all exact (((cxW R F u).iC F.cr bb A3.A.μ0 (cpt A3.A.v0.embedding (x ∘ Fin.cast h.symm))) :)))))) ∧
      ∀ v, Xo v = (((cxW R F u).data F.cr bb).XE v).submatrix (Fin.cast h) (Fin.cast h) ∧ IsUnit (Xo v).det) (parts_eq b R F) h

end
