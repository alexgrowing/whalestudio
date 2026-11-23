import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelColumnsFromTiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelCompatibilitiesStandardKernelDataTrueColumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerSizesOfStdKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamRowsSizes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSymmetricColumnFormsStepZeroFiniteCharacteStatement
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfBranchIdentitiesAndMultiplicity
import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.HeckeRamifiedZeroAll
import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.RL.DefSide

open Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory in

theorem full_rank {eps : ℝ} (Fm : FamP eps) (CH : ℝ) (tie : RealPlaceSecondLayerConditions Fm) (hTu : TuSize Fm) (hCh : ChosenE Fm 3 CH) :
    NuFullF Fm ∧ J.MuRank Fm := by
  have tT := (family_conditions_of_layer_two Fm tie).2.2
  have h := slope_free_branch_family Fm tT freeTT_holds slopeLineT_holds Formalism.L2.GlobalTheoryTheory.LemB.second_branch_all_members
  obtain ⟨hT2, hT5⟩ := Formalism.MainNotions.Wire.family_theorems_two_and_five Fm h.1 h.2.1 (hI_tied Fm tT PI.IntegralAtBasePointLattice.integral_at_t0_lattice)
    (tT.mono fun D u hS ht => Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.hecke_ramified_zero_all D u hS ht) h.2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, cPr, _⟩ := hCh
  exact muRank_items Fm 3 (by norm_num) hT2 hT5 hTu cPr

theorem wts_eq {X X' : Formalism.L2.Col.Fields} (h : X = X') {P : Formalism.L2.Col.Primes X} {P' : Formalism.L2.Col.Primes X'} (hP : HEq P P')
    {R R' : Ranks} (hR : R = R') : Formalism.L2.Col.Wts X P.Word R = Formalism.L2.Col.Wts X' P'.Word R' := by
  subst h; cases hP; subst hR; rfl

def PtE : BdP Bundle := fun D O _ b =>
  (Formalism.L2.Theta.RealTied D ∧ ∃ C : Formalism.L2.Forms.ColsTiedSym D, ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u)) ∧
  Formalism.L2.DIV.ColPins b.C.toS ∧ ∃ W : Formalism.L2.Col.Wts b.R.T.ker.X b.R.T.ker.Pr.Word D.R, HEq b.C.toS.c.W W ∧
    GlobalTheory.ColRows.KerTies b.R.T.ker W b.DH.1.1 b.DH.1.2 ∧
    ∀ CY CT : ℝ, GlobalTheory.CoreHt.HtRowsS O.L CY → 8 ≤ O.L.sc.X' → 2 ≤ O.L.sc.x → (∀ u, 4 * O.L.sc.a < ((D.mem u).A.T : ℝ)) →
      (∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * O.L.sc.L) →
      GlobalTheory.ColRows.KerSizes b.R.T.ker W b.DH.1.1 b.DH.1.2 CY CT

theorem ptE_of_wit {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (q : WPt p.s K) {c : ℝ}
    (b : Bundle (q.w.D q.Z) q.O c) (w : BWit q b) : PtE _ _ c b := by
  have hk := b.C.kerTie
  have e : Formalism.L2.Col.Wts _ b.C.c.Pr.Word b.C.c.Rk = Formalism.L2.Col.Wts b.R.T.ker.X b.R.T.ker.Pr.Word (q.w.D q.Z).R :=
    wts_eq hk.1.symm hk.2.2.1 hk.2.1
  have hW : HEq (cast e b.C.c.W) q.B.wts := (cast_heq e _).trans w.cW.1
  refine ⟨⟨q.x.real, GlobalTheory.T.exists_symmetricColumnForms_stepZeroFiniteCharacter q.w.I q.w.ok q.w.pins q.w.l q.Z⟩, w.colPins, cast e b.C.c.W, (cast_heq e _).symm, ?_, ?_⟩
  · exact GlobalTheory.T.kernelCompatibilities_standardKernelData_trueColumns q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex b.R.T.ker _ _ _ q.x.pin.jets w.recPin.k.std hW
      b.DH.2.1 b.DH.2.2 (b.R.T.ker_sharp _)
  · exact GlobalTheory.ColRows.kerSizes_of_stdKer q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex b.R.T.ker _ _ _ w.recPin.k.std hW
      b.DH.2.1 b.DH.2.2

theorem ptE_of_linked {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (β : BPt K) (c : ℝ) (b : Bundle β.D β.O c)
    (h : IsLinked p K β c b) : PtE _ _ c b := by
  obtain ⟨q, b', ⟨w⟩, e⟩ := h
  exact Eq.mpr (congrArg (fun y : Σ (D : D7) (O : Obj D), Bundle D O c => PtE y.1 y.2.1 c y.2.2) e) (ptE_of_wit q b' w)

theorem drs_pt (CY CT : ℝ) (hCT : 0 ≤ CT) : ∃ C0 : ℝ, ∀ (D : D7) (O : Obj D) (c : ℝ) (b : Bundle D O c) (C CH : ℝ),
    PtE D O c b → GlobalTheory.CoreHt.HtRowsS O.L CY → 8 ≤ O.L.sc.X' → 2 ≤ O.L.sc.x → (∀ u, 4 * O.L.sc.a < ((D.mem u).A.T : ℝ)) →
      (∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * O.L.sc.L) → DV.NprimeDef D O.L → D.NuFull →
      (∀ u, 0 < (D.div.Nu u).rank) → C0 ≤ c → DRS D O c b C CH := by
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.kernel_columns_from_ties CY CT hCT
  refine ⟨C0, fun D O c b C CH hE h1 h2 h3 h4 h5 hN hF hR hc => ?_⟩
  obtain ⟨-, hpin, W, hW, hT, hS⟩ := hE
  intro hok1 hsep hP hI lam0 c0 ce Sw C1 H NuC I _ hII u
  have hZs : (Formalism.L2.RowDataTransport.pkOf (qS b) hok1 hsep C CH hP hI).Zs = b.P.Zs := (qS b).zs
  have hS0 : HEq (Formalism.L2.RowDataTransport.pkOf (qS b) hok1 hsep C CH hP hI).core.base.toIndefData b.P.S0 := (qS b).s0
  have hS1 : HEq (Formalism.L2.RowDataTransport.pkOf (qS b) hok1 hsep C CH hP hI).core.cols.toIndefData b.P.S1 := (qS b).s1
  have hDc : HEq (b.C.toS.c.face (Formalism.L2.RowDataTransport.pkOf (qS b) hok1 hsep C CH hP hI).Zs) b.P.Dc :=
    (congr_arg_heq b.C.toS.c.face hZs).trans (heq_of_eq b.C.toS.colTie.1)
  have hw : HEq (I.wU u) u := ((Formalism.L2.DIV.divTieDat3_heq hZs hS0 hS1 hDc hII).2.2 u).trans (b.C.wTie u)
  exact hC0 D O.L _ _ _ _ _ _ O.ex b.R.T b.P b.C.toS W _ _ hpin hW hT (hS CY CT h1 h2 h3 h4 h5) hN hF hR _ _ C CH
    (Formalism.L2.RowDataTransport.pkOf (qS b) hok1 hsep C CH hP hI) hZs u lam0 c0 ce c Sw C1 (H u) (I.wU u) (I.eNu u) hw hc

theorem row_df {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) : RL.At p RL.DifferentialCondition := by
  refine RL.At.of_row (p := p) (H := Ind.EvWC (Bd := Bundle) (fun _ => True) fun C CH D O c b => DRS D O c b C CH)
    ⟨fun _ => PtE, RowE.of_all fun _ _ β c b _ _ h => ptE_of_linked β c b h, fun 𝒜 σ s => ?_⟩
  choose c0 hc0 using fun (CY CT : ℝ) => drs_pt CY (max CT 0) (le_max_right _ _)
  refine (Formalism.MainNotions.DIV.closed_Csz_ge_fn (W3 𝒜) fun l => c0 (l.getD 6 0) (l.getD 13 0)).imp ?_
  intro eps Fm CH _ hC hc _
  have hC' : c0 Fm.CYL Fm.CTu ≤ Fm.Csz := hC
  obtain ⟨κ, -, -, hs⟩ := s Fm (w3_a hc)
  have tie : RealPlaceSecondLayerConditions Fm := ⟨Fm.x1 + 1, fun x hx i => (hs x (by linarith) i).2.1⟩
  obtain ⟨CH', hCh⟩ := hc.2.1
  obtain ⟨⟨a1, hF⟩, ⟨a2, hR⟩⟩ := full_rank Fm CH' tie hc.2.2.1 hCh
  obtain ⟨a3, hz⟩ := GlobalTheory.CoreHt.famRowsSizes Fm hc.2.2.1
  refine ⟨0, le_rfl, fun C _ => ⟨max a1 (max a2 a3), fun x hx h0 i => ?_⟩⟩
  have e1 : a1 ≤ x := le_trans (le_max_left _ _) h0
  have e2 : a2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h0
  have e3 : a3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h0
  obtain ⟨z1, z2, z3, z4, z5⟩ := hz x e3 i ⟨_, (σ Fm (w3_a hc) x hx i).DH.2.1⟩
  exact hc0 Fm.CYL Fm.CTu _ _ _ (σ Fm (w3_a hc) x hx i) C CH (hs x hx i).2 z1 z2 z3 z4 z5 (Fm.nprimeDef x hx i)
    (hF x e1 i) (hR x e2 i) hC'

end GlobalTheory.Fc.RL.DefSide

theorem GlobalTheory.Fc.RL.at_row_df : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), RL.At (prmR N S Γ) RL.DifferentialCondition :=
  fun _ _ _ _ _ N S Γ => GlobalTheory.Fc.RL.DefSide.row_df (prmR N S Γ)

end
