import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGIsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonzeroForcedContentPlacesAgreeOverEnlargement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesEqUnionThreeParts
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapMemSpanImage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NontrivialReferenceForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsDivStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSStageTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemLevelOfLocalDepth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeBelow
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Second

theorem exists_lt_of_stage (hG : GlobalTheory.Published.GreenCuspidal) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)
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
  exact ⟨⟨W', V, S, N, G⟩, rfl, hN, GlobalTheory.Mem.R3.Model.grpAt_of_grpTrue (w.st ⟨W', V, S, N, G⟩) w.I w.ok
    (by show GrpTrue N w.I.C; rw [w.C_eq]; exact hN), hk w.C W' rfl rfl V S N G⟩

theorem exists_below_of_range (D D' : D7) (h : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (v' : D'.what₂.places.Pl) :
    ∃ v : D.what₂.places.Pl, Below D D' v v' := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.PrimeBelow.exists_below
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.PrimeBelow.exists_below
  | exact @_root_.GlobalTheory.PrimeBelow.exists_below
  | exact _root_.GlobalTheory.PrimeBelow.exists_below
  | (apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeBelow.exists_below <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeBelow.exists_below ..)

theorem resChar_of_below {D D' : D7} {v : D.what₂.places.Pl} {v' : D'.what₂.places.Pl} (hB : Below D D' v v') :
    D'.what₂.places.resChar v' = D.what₂.places.resChar v := by
  refine GlobalTheory.LvT.Inh.resChar_eq_of_mem_plEq D' v' (D.what₂.places.resChar_prime v) ((hB _ _ ?_).1 (GlobalTheory.LvT.Inh.resChar_mem_plEq D v))
  simp only [map_natCast]

theorem not_mem_W1F_zero (D : D7) (v : D.what₂.places.Pl) : v ∉ placesWithNonzeroContentOrConj D (fun _ _ => 0) := by
  rintro ⟨_, _, _, h⟩
  exact h rfl

end GlobalTheory.Mem.R3.Rw.Second

namespace GlobalTheory.Mem.R3.Rw.Second

theorem exists_ext_twisted_places : GlobalTheory.Published.GreenCuspidal → DatExt → StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Pinned K B f T w → HEq w'.px w.px → T'.pl = T.pl → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → Fine z → HoldsL z.R z.F → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) → (∀ (Z' : w'.Lt) v', (∀ v, Below (w.D Z) (w'.D Z') v v' → v ∉ Wt) → T'.psi v' = 1) → ∃ (Z' : w'.Lt) (hX' : B'.fields.Ok) (z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}), GIs2 K w' Z'.G ∧ GrpTrue Z'.N f' ∧ GrpAt (w'.st Z') w'.I ∧ DV.KapDef (w'.D Z') ∧ Fine z' ∧ (∀ v ∈ z'.W1 (F0K K.s (w'.D Z')), B'.places.resChar v ∈ T'.pl) ∧ (∀ v, v ∉ z'.W1 (F0K K.s (w'.D Z')) → T'.psi v = 1) ∧ Ext z z' ∧ ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ Wt ↔ v' ∈ z'.W1 (F0K K.s (w'.D Z'))) := by
  intro hG hDE
  have hP : StepW Pinned Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine ((hP.and hDE).and GlobalTheory.T.exists_GJStage_GIs2_pinned).trans (StepW.of_all fun K B' f' T' w' hO' _ H => ?_)
  obtain ⟨⟨⟨pin'⟩, hDE'⟩, G, hG2⟩ := H
  intro B f T w hE hf hPin hpx hpl Z hX Wt z hGT hGA hKap hFine hHL hWt hsub hpsi
  obtain ⟨Z', rfl, hGT', hGA', hKap'⟩ := exists_lt_of_stage hG w' hO' pin'.hX G
  obtain ⟨z', hFine', hExt⟩ := hDE' B f T w hE hf hPin hpx Z hX Wt z hGT hGA hFine hHL Z' pin'.hX hGT' hGA'
    (hG2 Z'.W Z'.V Z'.S Z'.N).1
  have key : ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ Wt ↔ v' ∈ z'.W1 (F0K K.s (w'.D Z'))) := by
    intro v v' hB
    have h0 := hExt.W1 v v' hB
    have a := Dat.mem_auxiliaryPlaces_iff_three_parts z (fun _ _ => 0) v
    have b := Dat.mem_auxiliaryPlaces_iff_three_parts z' (fun _ _ => 0) v'
    have i0 : (v ∈ z.IwasawaPlaceIndex ∨ v ∈ z.W1jw) ↔ (v' ∈ z'.IwasawaPlaceIndex ∨ v' ∈ z'.W1jw) :=
      ⟨fun h => (b.1 (h0.1 (a.2 (Or.inl h)))).resolve_right (not_mem_W1F_zero _ _),
        fun h => (a.1 (h0.2 (b.2 (Or.inl h)))).resolve_right (not_mem_W1F_zero _ _)⟩
    have c := Dat.mem_auxiliaryPlaces_iff_three_parts z (F0K K.s (w.D Z)) v
    have d := Dat.mem_auxiliaryPlaces_iff_three_parts z' (F0K K.s (w'.D Z')) v'
    have e := nonzeroForcedContentPlaces_agree_over_enlargement K B f T w B' f' T' w' hE Z Z' hKap hKap' v v' hB
    rw [hWt]
    exact c.trans ((or_congr i0 e).trans d.symm)
  refine ⟨Z', pin'.hX, z', hG2, hGT', hGA', hKap', hFine', ?_, ?_, hExt, key⟩
  · intro v' hv'
    obtain ⟨v, hB⟩ := exists_below_of_range (w.D Z) (w'.D Z') hE.2.2.2 v'
    have hv := (key v v' hB).2 hv'
    have hr := resChar_of_below hB
    rw [hpl]
    exact hr ▸ hsub v hv
  · intro v' hv'
    exact hpsi Z' v' fun v hB hv => hv' ((key v v' hB).1 hv)

end GlobalTheory.Mem.R3.Rw.Second
