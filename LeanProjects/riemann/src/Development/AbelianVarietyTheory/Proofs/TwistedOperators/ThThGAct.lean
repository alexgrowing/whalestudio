import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProjectionIntertwinesLevelLiftsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslateLiftV

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.LiftGroupEquiv.th_thG_act : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ t (g : G) (x : (A.fam.R t).S.Forms), R.Th t (R.jX t ((A.fam.R t).r g x)) = R.gE g (R.Th t (R.jX t x))) ∧ ∀ i t (g : G) (x : (A.fam.L i t).S.Forms), R.thG i t (R.jV i t ((A.fam.L i t).r g x)) = R.gW i (sg0 D A) g (R.thG i t (R.jV i t x)) := by
  intro hP D G _ _ Pl0 T0 A Ks _ _ _ R F hC
  have hRr : R.grp_red_R := hC.grp.red_R
  have hRl : R.grp_red_L := hC.grp.red_L
  have hMx : R.models_jX := hC.models.jX
  have hMv : R.models_jV := hC.models.jV
  refine ⟨fun t g x => ?_, fun i t g x => ?_⟩
  · have H1 := @GlobalTheory.FormAction.act_eq_translate D G _ _ Pl0 T0 A Ks _ _ _ R hRr hMx t g x
    exact H1.elim fun κ hh =>
      @GlobalTheory.T.chainCompositeLift_intertwines_finiteGroupActions D G _ _ Pl0 T0 A Ks _ _ _ R F hC.lev hC.grp hC.fam hC.models hC.chain
        (fun t j _ => GlobalTheory.MultFinite.schurMult hP _ _) t g κ hh.1 _ _ hh.2
  · have H2 := @GlobalTheory.RationalFormsAction.act_eq_translate_lift_V D G _ _ Pl0 T0 A Ks _ _ _ R hRl hMv i t g x
    exact H2.elim fun κ hh => @GlobalTheory.T.thetaProjection_intertwines_levelLifts D G _ _ Pl0 T0 A Ks _ _ _ R F hC i t g κ hh.1 _ _ hh.2
