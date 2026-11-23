import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionCompatibleAtReadIdentificationsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionPairingRationalOnRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLatticesMetricsAgreeOfRealGroupTheoremsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingDefiniteBaseVanishOfMiStar2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeOpEqSpanOfFormsTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.CutPassage
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalRingCardinality.DataBu
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF

noncomputable section

namespace GlobalTheory.Fc.DivLinked

section Read

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Matrix Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}

set_option maxHeartbeats 2000000 in

theorem divisionRows_pairing_vanishes_of_rational_pairing_law
    (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧
      GlobalTheory.Published.CuspRapidDecay) (x : TwIn ex) (hH : Holds x.R x.F) (hB : Rw.BkLaw D)
    (hV : CxData.BtVanish (fc := x.F.fc) (x.R.toCx3 x.F)) : GlobalTheory.Cp.DivRows3G (divisionPairOfAdelicFormsFaceColumnsData x) :=
  (GlobalTheory.Cp.divRows3G_iff _).2 ((rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ x).2.2.2
    ((GlobalTheory.T.divisionCompatible_at_readIdentifications hC D x.G x.Pl0 x.I0 x.T x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.C x.sEE Yd x.JM x.pins hH fun _ _ => x.div.grp).2
      x.mjH ex.idx (hB (GlobalTheory.T.divisionPairing_rational_on_rationalPoints' hC D x.G x.Pl0 x.I0 x.T x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.C x.pins hH)) hV))

end Read

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

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

section Wit

variable (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
  GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
  {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : Bundle (q.w.D q.Z) q.O c}

include hC

theorem div_of_mi (w : BWit q b) (hB : R3.Rw.BkLaw (q.w.D q.Z))
    (hM : (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) : R1.P_hDivG _ _ c b := by
  have h : (fun r : RPk b.R b.S => (r.B.Q.Rl.toCx3 r.B.Q.F).MIstar2 (r.B.Q.F.eV (r.B.Q.Rl.toCx3 r.B.Q.F).zs) r.B.Q.sEE →
      GlobalTheory.Cp.DivRows3G r.P) (rpkX w.y.y) := fun hM =>
    divisionRows_pairing_vanishes_of_rational_pairing_law hC w.x w.y.intersectionNumber_baseChange hB
      (GlobalTheory.Div.pairing_definite_base_vanish_of_miStar2 _ _ _ _ _ w.x.A3 _ w.x.R w.x.F 1 w.y.intersectionNumber_baseChange.ok w.y.intersectionNumber_baseChange.sep w.x.pins.char
        w.y.intersectionNumber_baseChange.prim w.x.sEE hM)
  rw [← w.y.eq] at h
  exact h hM

end Wit

theorem at_hDivG_of_mi (h1 : GlobalTheory.Published.DiscreteSeriesCover) (h2 : GlobalTheory.Published.HarishChandraModules) (h3 : GlobalTheory.Published.CasselmanWallach)
    (h4 : GlobalTheory.Published.HarishChandraFinite) (h5 : GlobalTheory.Published.CuspRapidDecay) (p : Prm hL)
    (hB : ∀ (K : Ctx) (q : WPt p.s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z))
    (hM : RL.At p fun Q L => Row Q L (AtAll fun _ _ _ (b : Bundle _ _ _) =>
      (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) : RL.At p R1.DivisorConditionAtBundlePoints :=
  at_atAll (R := R1.P_hDivG) (fun K q _ _ w h => div_of_mi ⟨h1, h2, h3, h4, h5⟩ w (hB K q) h) hM

theorem at_hDivG_main : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ (K : Ctx) (q : WPt (prmR N S Γ).s K), GlobalTheory.Mem.R3.Rw.BkLaw (q.w.D q.Z)) → RL.At (prmR N S Γ) (fun Q L => Row Q L (AtAll fun _ _ _ (b : Bundle _ _ _) => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) → RL.At (prmR N S Γ) R1.DivisorConditionAtBundlePoints :=
  fun _ _ h3 h4 h5 h6 h7 _ _ _ _ hB hM => at_hDivG_of_mi h5 h6 h7 h3 h4 _ hB hM

end GlobalTheory.Fc.DivLinked

end
