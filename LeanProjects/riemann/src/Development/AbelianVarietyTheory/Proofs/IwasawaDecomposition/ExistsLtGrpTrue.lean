import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NontrivialReferenceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapMemSpanImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsDivStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem holdsLU_stepW (h : LowerUnitaryCaseCondition) : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo →
    HoldsL z.R z.F := h

theorem exists_lt_grpTrue (hG : GlobalTheory.Published.GreenCuspidal) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)
    (hO : K.Over B.toPre) (hX : B.fields.Ok) (G : GJStage B w.C) :
    ∃ Z : w.Lt, Z.G = G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) := by
  obtain ⟨R⟩ := GlobalTheory.Mem.Df.rowsDef_nonempty w.I w.ok w.pins w.l hX
  obtain ⟨kb, ks, hk⟩ := GlobalTheory.Mem.Df.Model.exists_ka B
  let W' : RowsRest B w.C :=
    { R.W with
      eOp := fun _ => 0
      eOp_idem := fun _ => LinearMap.comp_zero _
      eOp_sa := fun _ => LinearMap.IsSymmetric.zero
      kaBig := kb
      kaSmall := ks }
  obtain ⟨V, -⟩ := GlobalTheory.Mem.DivModel.exists_divStage B w.C W'
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C W' G.cd hO (GlobalTheory.Mem.Df.cols_pos w.I w.ok w.pins w.l hX)
    (show R.W.Drows ≤ R.W.Dall by rw [R.std.drows, R.std.dall])
  have hMt : ∀ (μ : w.C.Tup) (j : ℕ), W'.eMt μ j = 0 := fun μ j => by
    haveI := R.std.mt μ j
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  obtain ⟨N, -, -, hN, -⟩ := GlobalTheory.Mem.Top.exists_nStage_grpTrue hG B w.C W' R.std.sha (fun j v _ _ => R.std.eta j v)
    (fun _ => rfl) hMt f
  refine ⟨⟨W', V, S, N, G⟩, rfl, hN, GlobalTheory.Mem.R3.Model.grpAt_of_grpTrue (w.st ⟨W', V, S, N, G⟩) w.I w.ok (by show GrpTrue N w.I.C; rw [w.C_eq]; exact hN),
    hk w.C W' rfl rfl V S N G⟩

end GlobalTheory.Mem.R3.Rw
