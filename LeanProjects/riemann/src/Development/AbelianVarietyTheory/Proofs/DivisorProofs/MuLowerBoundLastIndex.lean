import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeSlopeLowerBoundDefiniteCaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationCaseFiniteComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGroupLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatExistsAtLastIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuBoundNotAlgebraicallyClosedStatement
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.DefCore

theorem connected_case : Hypotheses2 → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  intro _hP
  refine ⟨0, 0, le_rfl, ?_⟩
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A hp hi hg hw hh hF
  obtain ⟨hdef, hfin, hne, hdict⟩ := GlobalTheory.T.deformation_case_finite_components p i PP A 0 hp hi hg hw hh hF
  obtain ⟨G, _, _, lev, χ, hact, hfree, hsl⟩ := GlobalTheory.T.exists_finite_group_level p i PP A 0 hp hi hg hw hh hF
  have hflat := GlobalTheory.T.flat_exists_at_last_index p i PP A 0 hp hi hg hw hh hF
  have h := (GlobalTheory.T.eigenlattice_slope_lower_bound_definite_case D _ _ _ _ _ _ (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) G lev χ
    (wtA (p.κ i)) (p.κ i).n _ hdef hfin hne hdict hact hfree hw.dom hg.2.2.2 hflat).2
  unfold Gk at hsl
  linarith

theorem unitE_nonneg {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (i : Fin D.R.m) (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) : 0 ≤ unitE p := by
  rw [hw.unit]
  have hx : 0 < L.sc.x := by linarith [hh.big.2.1, hh.big.2.2.1]
  have hb : 0 < L.sc.b := lt_of_lt_of_le (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hx _) _) hh.room
  have := hh.big.2.2.2
  have : (0:ℝ) ≤ L.sc.L := by linarith [hh.big.2.1]
  positivity

theorem twice_defBound_le_muCore : Hypotheses2 → Lifts fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → GramAt p i → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm) - C * unitE p ≤ muCore p i := by
  intro hP
  obtain ⟨M1, C1, hC1, h1⟩ := connected_case hP
  obtain ⟨M2, C2, hC2, h2⟩ := GlobalTheory.T.mu_bound_not_algebraically_closed hP
  have hW : WtN := GlobalTheory.CovTop.WtShape.wtN
  have hH1 : HostN M1 := GlobalTheory.CovTop.Sizes.hostN M1
  have hH2 : HostN M2 := GlobalTheory.CovTop.Sizes.hostN M2
  unfold Lifts WtN HostN at *
  refine Closed.imp ((hW.and hH1).and hH2) ?_
  rintro eps Fm CH - ⟨⟨⟨Cw, -, xw, hw⟩, ⟨A1, -, x1, ha1⟩⟩, ⟨A2, -, x2, ha2⟩⟩
  refine ⟨max C1 C2, le_max_of_le_left hC1, max (max xw x1) x2, fun x hx hle ι p hp i hi hg => ?_⟩
  have hle1 : xw ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hle2 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have hle3 : x2 ≤ x := le_trans (le_max_right _ _) hle
  have w := hw x hx hle1 ι p hp i
  have a1 := ha1 x hx hle2 ι p hp i
  have a2 := ha2 x hx hle3 ι p hp i
  have hu := unitE_nonneg p i _ _ _ w a1
  by_cases hF : FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
  · have := h1 p i _ _ hp hi hg w a1 hF
    nlinarith [le_max_left C1 C2]
  · have := h2 p i _ _ hp hi hg w a2 hF
    nlinarith [le_max_right C1 C2]

end GlobalTheory.CovTop.DefCore

end
