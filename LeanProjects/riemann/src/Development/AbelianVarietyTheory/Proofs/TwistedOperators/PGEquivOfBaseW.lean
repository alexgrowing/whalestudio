import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThThGAct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GEquivCx

set_option maxHeartbeats 400000 in

theorem pGEquiv_of_baseW : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.toRealDat.BaseW F.lv2 → R.toRealDat.ExAt → R.PGEquiv F := by
  intro hCR D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hB hE
  have hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2 :=
    ⟨hB.lev, hB.grp, hB.fam, hB.models, RealDat.chain_of_weak hB.chain hE, RealDat.thP_of_weak hB.thP hE⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.LiftGroupEquiv.th_thG_act hCR R.toRealDat F.lv2 hC
  refine ⟨fun t g x => ?_, fun j t g x => ?_⟩
  · exact h1 t g x
  · have e : cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j t (R.jV j t ((A3.A.fam.L j t).r g x)) =
        R.gW j (sg0 D A3.A) g (cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j t (R.jV j t x)) :=
      (congrArg (fun y => cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • y) (h2 j t g x)).trans
        (LinearMap.map_smul _ _ _).symm
    exact e

end GlobalTheory.GEquivCx
