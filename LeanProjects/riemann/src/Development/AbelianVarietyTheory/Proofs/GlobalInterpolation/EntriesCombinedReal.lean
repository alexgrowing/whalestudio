import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JoinSubspaceRealDataExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLatticesMetricsAgreeOfRealGroupTheorems
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpectralStagePointRowPlacementTransfer

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.JoinLinked

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem move {D : D7} {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F0 = F0')
    (Φ : ∀ F : (∀ u, Formalism.L2.Forms.Forms0 D u), ∀ P : GlobalTheory.Mem.SRe.SPack D F, GlobalTheory.Mem.SRe.SRest P → Formalism.L2.Theta.GA D (D.sp.Y 0) → ℝ → Prop)
    {P' : GlobalTheory.Mem.SRe.SPack D F0'} {S' : GlobalTheory.Mem.SRe.SRest P'} {t t' : Formalism.L2.Theta.GA D (D.sp.Y 0)} {c c' : ℝ}
    {P : GlobalTheory.Mem.SRe.SPack D F0} {S : GlobalTheory.Mem.SRe.SRest P} (hP : HEq P P') (hS : HEq S S') (ht : HEq t t') (hc : c = c')
    (h : Φ F0' P' S' t' c') : Φ F0 P S t c := by
  subst hF
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hS
  obtain rfl := eq_of_heq ht
  subst hc
  exact h

theorem schurAll (hH : GlobalTheory.Published.HarishChandraFinite) (hC : GlobalTheory.Published.CuspRapidDecay) (D : D7) :
    Formalism.IndefR.Links.SchurAll D :=
  fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2

section IndefiniteRowSideFullHecke

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation
  Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}

theorem join_linked_realization (hR : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    (x : TwIn ex) (Rc : Formalism.L2.RecT ex) (S0 : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (P : SPack D fun u => (Rc.T.cols.forms u).to0)
    (S : SRest P) (hS0 : S0 = S.toSTiesR Rc) (y : RealIn x Rc S0) (c : ℝ) (hPins : RealPins (realTOf y)) (hH : Holds x.R x.F)
    (hSee : SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS)
    (hEv : EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G
      (iotaX P.X P.inst).toMulEquiv y.tS c)
    (hRow : RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j) :
    Nonempty (Formalism.L2.SG.JoinSI.JoinSI Rc S0 (realTOf y)) := by
  subst hS0
  have hRR := (GlobalTheory.Mem.R3.rowLat_ties hR _ _ _ _ _ x.A3 _ x.R x.F x.cG _ x.Y x.Z x.pins hH).1
  exact (GlobalTheory.Mem.KJoinLat.join_subspace_real_data_lattice D L hT Gi Gl K Yd cX ex x Rc P S y c 1 (schurAll hR.2.2.2.1 hR.2.2.2.2 D) hPins hH hH.ok hH.sep hRR
    (rowConditions_at_companion_from_readings D L hT Gi Gl K Yd cX ex x).2.1 hSee hEv hRow).1

end IndefiniteRowSideFullHecke

section Wit

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation
  Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.SRe

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL}

set_option maxHeartbeats 2000000 in

theorem selJ_of_wit (hR : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : Bundle (q.w.D q.Z) q.O c} (w : BWit q b) (t : b.Comparison₂) : R1.P_selJ _ _ c b := by
  show Nonempty (Formalism.L2.SG.JoinSI.JoinSI (R := b.R) (S := b.S) (Q := b.B.Q))
  have hPins : RealPins (R3.realTOf w.y.y) := by
    have h : (fun r : RPk b.R b.S => RealPins r.B.Q) (rpkB b) := t.pins
    rw [w.y.eq] at h
    exact h
  obtain ⟨sP, sS, hP, hS, hSeq⟩ := w.s
  have hx : w.a.x = w.x := eq_of_heq w.ax
  have hM := GlobalTheory.Mem.R3.StageMove.spectralStage_point_rowPlacement_transfer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w.a _ q.sat
  rw [hx] at hM
  have hF : (fun u => (b.R.T.cols.forms u).to0) = fun u => (q.x.col.C.forms u).to0 := by
    rw [w.recPin.s.cols]
  have hN := move hF (fun _ P S t c => SeeAt w.x.R.toRealDat w.x.F.lv2 P.X P.inst t ∧
      EvalTieT (MP w.x.R.toRealDat) w.x.R.toRealDat.ν0 w.x.R.toRealDat.fd0 (EP w.x.R.toRealDat w.x.F.lv2) P.X P.G
        (iotaX P.X P.inst).toMulEquiv t c ∧ RowJ w.x.R.toRealDat w.x.Y.eE P.X P.inst P.G t S.j)
    (P := sP) (S := sS) (t := w.y.y.tS) (c := w.y.y.cS) hP hS w.pt.1 w.pt.2 hM
  have hJ := join_linked_realization hR w.x b.R b.S sP sS hSeq w.y.y w.y.y.cS hPins w.y.intersectionNumber_baseChange hN.1 hN.2.1 hN.2.2
  have h : (fun r : RPk b.R b.S => Nonempty (Formalism.L2.SG.JoinSI.JoinSI (R := b.R) (S := b.S) (Q := r.B.Q))) (rpkX w.y.y) := hJ
  rw [← w.y.eq] at h
  exact h

end Wit

section Constructions₂

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL}

theorem of_built {R : BdP Bundle} {Q : V4.Slot} {κ : Par}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c), BWit q b → R _ _ c b)
    {D : D7} {O : Obj D} {c : ℝ} {b : Bundle D O c} (hb : GlobalTheory.Fc.Built Q (IsLinked p) κ D O c b) : R D O c b := by
  refine GlobalTheory.Fc.Built.ind (R := R) (fun K β c b _ _ hl => ?_) hb
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => R s.1 s.2.1 c s.2.2) he
  exact cast this.symm (h K q c b' w)

theorem at_atAll {A R : BdP Bundle}
    (h : ∀ (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c), BWit q b → A _ _ c b → R _ _ c b)
    (hA : RL.At p fun S L => Row S L (AtAll A)) : RL.At p fun S L => Row S L (AtAll R) := by
  obtain ⟨S, hS, hA⟩ := hA
  refine ⟨S, hS, Row.imp hA fun 𝒜 σ s H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨κ, -, -, t⟩ := s Fm hc
  exact of_built (R := fun D O c b => A D O c b → R D O c b) h (t x hx i).1 (H Fm hc x hx i)

end Constructions₂

theorem at_selJ : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.DiscreteSeriesCover →
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), RL.At (prmR N S Γ) R1.PeriodAdmissibilityAtBundlePoints →
    RL.At (prmR N S Γ) R1.DecompositionConditionAtBundlePoints → RL.At (prmR N S Γ) RL.Row_tie → RL.At (prmR N S Γ) R1.JSelectionAtBundlePoints :=
  fun _ _ h1 h2 h3 h4 h5 _ _ _ _ _ _ hT =>
    at_atAll (A := HasTie) (R := R1.P_selJ) (fun _ _ _ _ w ht => selJ_of_wit ⟨h1, h2, h3, h4, h5⟩ w (Classical.choice ht)) hT

end GlobalTheory.Fc.JoinLinked

end
