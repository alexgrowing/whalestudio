import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JoinArrows

theorem weil_arrow_transport {D : D7} {ψ : AddChar (AF ↥D.host.F) ℂ} {S T S' T' : HSp D}
    (hS : S = S') (hT : T = T') {χS χT χS' χT' : (AE D)ˣ →* Circle} (h1 : χS = χS') (h2 : χT = χT')
    (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS' χT' ω') :
    ∃ ω : GlobalTheory.Grid.WRep S T, GlobalTheory.Grid.IsWeil ψ false S T χS χT ω ∧ HEq ω ω' := by
  cases hS
  cases hT
  cases h1
  cases h2
  refine ⟨ω', ?_, HEq.rfl⟩
  rw [GlobalTheory.Grid.isWeil_false]
  exact h

theorem exists_weil_rowArrow : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) i j, i + 1 ≤ D.R.m → j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) ω ∧ HEq ω (W.om (.mu t (i + 1) j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hSp _ hAg _ t i j hi hj

  have hw := W.om_is (.mu t (i + 1) j) ⟨hi, hj⟩
  rw [hW.ψ] at hw

  have e1 : (G.nV i j).V = G'.V (.grid (i + 1) j) := (hAg.vert (i + 1) j hi (by omega)).sp
  have e2 : (G.nV i (j + 1)).V = G'.V (.grid (i + 1) (j + 1)) := (hAg.vert (i + 1) (j + 1) hi hj).sp

  have r1 : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j := by
    rw [← e1]; exact (hSp.vert i j hi (by omega)).rank
  have r2 : (G'.V (.grid (i + 1) (j + 1))).rank = rkV D (i + 1) (j + 1) := by
    rw [← e2]; exact (hSp.vert i (j + 1) hi hj).rank

  have c1 : GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j) = G'.chrS (.mu t (i + 1) j) := by
    show _ = Formalism.IndefR.Lift.attChr _ _ (G'.V (.grid (i + 1) j)).rank
    rw [r1]
    rfl
  have c2 : GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1)) = G'.chrT (.mu t (i + 1) j) := by
    show _ = Formalism.IndefR.Lift.attChr _ _ (G'.V (.grid (i + 1) (j + 1))).rank
    rw [r2]
    rfl
  exact weil_arrow_transport e1 e2 c1 c2 (W.om (.mu t (i + 1) j)) hw

end GlobalTheory.JoinArrows
