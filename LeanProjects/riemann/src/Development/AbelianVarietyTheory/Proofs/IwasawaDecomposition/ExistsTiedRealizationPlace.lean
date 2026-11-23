import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalLanglandsPlaceDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTypesOfTypesTrueReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientFieldEqLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XiCharacterMatchesTypeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaEigenvalueGapBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesTrueLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigenIndexLabelingAtMemberStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAgreeRealOfReadGaloisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadOfEigenLabelingStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open RealOfReading

theorem tied_of_layer : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ X : GlobalTheory.NRows.Tied hL (w.D Z), PinAt c.a X.P ∧ HEq X.X.R t.r.z.R.toRealDat := by
  intro hP hL
  refine Model.AtMem.imp (Model.AtMem.and (GlobalTheory.T.exists_local_langlands_place_datum hP hL) (Model.AtMem.and (GlobalTheory.T.coefficient_field_eq_level hP hL)
    (Model.AtMem.and (GlobalTheory.T.xi_character_matches_type hP hL) (Model.AtMem.and (GlobalTheory.T.theta_eigenvalue_gap_bound hP hL)
    (Model.AtMem.and (GlobalTheory.T.types_true_local hP hL) (Model.AtMem.and (GlobalTheory.T.exists_eigen_index_labeling_at_member hP hL)
    (Model.AtMem.and (GlobalTheory.T.nonempty_agree_real_of_read_galois hP hL) (GlobalTheory.T.realOfRead_goodIdempotent_of_labelling hP hL)))))))) ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨P, hPin⟩, hC, htup, ⟨hPar, hGap⟩, hTT, ⟨Xd, E, ⟨labPi⟩⟩, hAg, hE0⟩
  have hg : GlobalTheory.LiftRows.Given t.r.z.R.toRealDat t.r.z.F.lv2 :=
    ⟨(GlobalTheory.CoreOfWeak.core_of_weak t.r.z.R t.r.z.F t.r.z.pins.char t.exAt).1, hPar, t.r.intersectionNumber_baseChange.ok.ok2.irr,
      GlobalTheory.HeightCounting.goodTypes_of_typesTrue_real _ _ _ _ _ _ _ t.r.z.pins.char.base.lev hTT, t.r.z.pins.keep.guard, hGap⟩
  obtain ⟨ag⟩ := hAg hC Xd E labPi t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP
  obtain ⟨T0, hT0, hR⟩ := exists_tied P (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi
    t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP) hPin.cf_eq hPin.C_eq hPin.tp_eq
    hPin.M_eq (hPin.rep_eq.trans c.row.rep_eq) ag (hE0 hC Xd E labPi t.r.z.pins.char.base htup hg t.r.z.pins.char.fullP)
  exact ⟨T0, by rw [hT0]; exact hPin, hR⟩

end GlobalTheory.HeightCounting.Up

end
