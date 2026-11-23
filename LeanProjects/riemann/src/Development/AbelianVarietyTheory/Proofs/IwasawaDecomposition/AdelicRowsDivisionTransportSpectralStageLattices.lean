import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxDefsUp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicRowsDivisionOverReplacedLaterStagesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHermitianLatticesReplacedStagesEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCompatibilitiesTransportReplacedStagesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up

set_option maxHeartbeats 4000000 in

theorem rows_up_at : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  intro K B f T w Z Wt p0 t S' N h
  obtain ⟨⟨z', hold', Y', Z'', tup'⟩, hz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    GlobalTheory.T.exists_adelicRowsDivision_over_replacedLaterStages B w.C Z (refUp Z S' N h) _ w.I t.hX T Wt (Equiv.refl _) p0 t.r
  subst hz
  let r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I t.hX T Wt (Equiv.refl _) (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0) :=
    ⟨_, hold', Y', Z'', tup'⟩
  have eW1 := Mv.forcedContentPlaces_eq_transport_sameFiniteGroup (refUp Z S' N h).to (refUp Z S' N h).same t.r.z (F0K K.s (w.D (SRe.upL Z S' N h)))
  let t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (refUp Z S' N h) p0) :=
    { hX := t.hX
      r := r'
      exAt := Mv.cp_exAt _ _ _ t.exAt
      inGeo := Mv.cp_inGeo _ _ _ t.inGeo
      grpAt := grpAt_up S' N h t.grpAt
      grp := t.grp
      mu := muIsW_up S' N h t.mu
      exact := (@Eq.trans (Set (@Rows.Places.Pl B.LL B.instLL B.places)) Wt (@Dat.W1 (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t)) (F0K K.s (@ColW.D B f T w Z))) (@Dat.W1 (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Mv.cpDat B (@ColW.C B f T w) Z (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Refill.same B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t))) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) (@RowsT.exact B f T K w Z Wt p0 t) (@Eq.symm (Set (@Rows.Places.Pl (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.LL (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.instLL (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))).B.places)) (@Dat.W1 (@Late.st B (@ColW.C B f T w) (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h))) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Mv.cpDat B (@ColW.C B f T w) Z (@Refill.to B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@Refill.same B (@ColW.C B f T w) Z (@refUp B f T w Z S' N h)) (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t))) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) (@Dat.W1 (@Late.st B (@ColW.C B f T w) Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (@RowsAre.z (@ColW.st B f T w Z) (@ColW.px B f T w) (@ColW.I B f T w) (@RowsT.hX B f T K w Z Wt p0 t) T Wt (Equiv.refl (@Cols0.Tup (@ColW.st B f T w Z).B.toPre (@Cols.toCols0 (@ColW.st B f T w Z).B (@ColW.st B f T w Z).C))) p0 (@RowsT.r B f T K w Z Wt p0 t)) (F0K K.s (@ColW.D B f T w (@SRe.upL B (@ColW.C B f T w) Z S' N h)))) eW1))
      untw := (t.untw)
      emt0 := (t.emt0)
      emt := (t.emt)
      etaF := t.etaF
      rowInt := rowInt_up S' N h t.rowInt
      idx := fun Y hY => idxDefs_up (Z := Z) (S' := S') (N := N) (h := h) Y
        (t.idx (divBack Y) (GlobalTheory.T.liftHermitianLattices_replacedStages_eq K B f T w Z t.hX Wt p0 t.r S' N h r' rfl h13 Y hY)) }
  have hs : RowsSame t t' :=
    ⟨rfl, rfl, HEq.rfl, HEq.rfl, (HEq.refl t.r.z.cG), h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  refine ⟨t', hs, (by with_unfolding_all exact ((HEq.refl (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo)) :)), ?_, GlobalTheory.T.rowCompatibilities_transport_replacedStages K B f T w Z Wt p0 t S' N h t' hs⟩
  exact (by with_unfolding_all exact ((congrArg (fun e => ({ (SRe.pkOf t).up Z S' N h with eE := e } : SRe.RowPk (SRe.upL Z S' N h).D)) (eq_of_heq h8)) :))

theorem rows_up : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ (p0' : BaseLevelRowSide (w.D (SRe.upL Z S' N h))) (t' : RowsT K w (SRe.upL Z S' N h) Wt p0'), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := fun K B f T w Z Wt p0 t S' N h =>
  let ⟨t', h1, h2, h3, h4⟩ := rows_up_at K B f T w Z Wt p0 t S' N h
  ⟨_, t', h1, h2, h3, h4⟩

end GlobalTheory.Mem.R3.Rw.Up
