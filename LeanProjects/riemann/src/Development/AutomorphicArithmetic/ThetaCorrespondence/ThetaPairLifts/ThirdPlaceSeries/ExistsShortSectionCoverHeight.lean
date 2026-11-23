import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsShortSectionCoverHeight
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ErrorBudgetCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ

set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.ShortPf
section Point
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
set_option maxHeartbeats 800000 in
theorem cover_height_short_section_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovHt.ShortAlt := fun hP _ _ hF => by
  obtain ⟨C, hC, H3⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison hP
  refine Closed.imp (Closed.and (Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1) _root_.GlobalTheory.CovTop.WtShape.wtN_z) hF) fun Fm _ _ h => ?_
  obtain ⟨⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩, ⟨_, _, h3⟩⟩ := h
  obtain ⟨x0, h⟩ := (h1.and h2).and h3
  refine ⟨C * 693, by positivity, x0, fun x hx hle ι p hp i hi Y hY u1 hq => ?_⟩
  obtain ⟨⟨g1, g2⟩, g3⟩ := h x hx hle ι p hp
  have hH := g1 i
  have hw := g2 i
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := weight_rows p i hH hw hi u1 hq
  have hL := hH.big.2.1
  have hM : Real.log Y.d.l₂.M ≤ 30 * (Fm.L x ι).sc.L := by
    rw [hY.1.lev.1.2.1, hY.1.pd, p.fw.laws.pins.2.1.1]
    exact log_level hH
  have key := H3 _ p.T p.fw.laws _ a1 a2 (by rw [hH.deg]; have := hH.f8; omega) ⟨by omega, hi.le⟩ Y _ _ hY.1 _ (by linarith) hM
    (fieldSz_host hH) hH.logfr.1 le_rfl _ (g3 i hi Y hY) (by rw [abs_neg]; exact FlatSz.abs_flatDegVal_le p i hH hw) u1 a3
    (fun τ => by
      unfold GlobalTheory.CompHS.gap
      rw [dif_pos (by show (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q; omega)]
      exact a4 τ _ _ rfl (by show (dat p i).p - 1 + 1 = _; omega)) a5
  refine ⟨Real.exp (C * ((((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 3 * (∑ τ, ∑ k, |(u1 τ k : ℝ)|) +
    (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 5)), fun Z => ?_, ?_⟩
  · obtain ⟨n, w, abelian₂, hs, hl, -⟩ := key Z
    have := (Real.log_le_iff_le_exp (lt_of_lt_of_le one_pos hs.one_le)).1 hl
    exact ⟨n, w, hs.gen, fun k σ => (hs.le k σ).trans this, hs.one_le.trans this⟩
  · rw [Real.log_exp, mul_assoc, mul_assoc C]
    exact mul_le_mul_of_nonneg_left a6 hC
end GlobalTheory.CovHt.ShortPf
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_short_of_deep_size_flatDeg : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovHt.ShortAlt := by
  first | exact @_root_.GlobalTheory.CovHt.ShortPf.cover_height_short_section_alt | exact _root_.GlobalTheory.CovHt.ShortPf.cover_height_short_section_alt | (intros; apply _root_.GlobalTheory.CovHt.ShortPf.cover_height_short_section_alt <;> assumption)
end
end
