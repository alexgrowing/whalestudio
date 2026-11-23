import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterMatchesWitnessStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistCharacterMatchesWitnessStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlacesMatchWitnessStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelTrueOfWitnessStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDataOfWitnessStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelMatchOfWitnessStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Fam.realAt_cols : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → (∀ j : Fin q.B.R.m, Formalism.IndefR.Links.ChrEq ((pk (packB b)).mu0 ((j : ℕ) + 1)) (q.w.I.C.mu0 j)) ∧ (∀ t, Formalism.IndefR.Links.ChrEq ((pk (packB b)).xi t) (q.w.I.xi (b.P.I.tup t))) ∧ (∀ t PP, PP ∈ (pk (packB b)).Q t ↔ PP ∈ Formalism.L2.Col.QE q.w.I.sel (q.w.I.tup (b.P.I.tup t) : Formalism.L2.DIV.Chr q.B.fields.F q.B.fields.E q.B.fields.K)) ∧ LevTrue (packB b) ∧ Nonempty (Formalism.IndefR.RealRec b.B.Q) ∧ Formalism.IndefR.RealPins b.B.Q ∧ (∃ s, b.P.A3.fam3.Ok3 s) ∧ GlobalTheory.Core.Mi.IdE b.S.X ∧ ∀ u, Formalism.L2.SG.ColDict.LevelMatch b.S.X (b.S.tr u) b.S.Y.hK := by
  intro hL p K q c b hw
  refine ⟨GlobalTheory.T.chrEq_mu0_of_bWit q b hw, GlobalTheory.T.twist_character_matches_witness q b hw, GlobalTheory.T.twist_places_match_witness q b hw, GlobalTheory.T.level_true_of_witness q b hw, ?_,
    GlobalTheory.T.real_data_of_witness q b hw, ⟨1, b.C.ok1⟩, (GlobalTheory.T.level_match_of_witness q b hw).1, (GlobalTheory.T.level_match_of_witness q b hw).2⟩
  obtain ⟨x, a, ax, y, recPin, s, pt, sx, eF, cW, d3b, side, colPins⟩ := hw
  show (fun k : Bl.RPk b.R b.S => Nonempty (Formalism.IndefR.RealRec k.B.Q)) (Bl.rpkB b)
  rw [y.eq]
  exact ⟨R3.realRecOf y.r⟩
