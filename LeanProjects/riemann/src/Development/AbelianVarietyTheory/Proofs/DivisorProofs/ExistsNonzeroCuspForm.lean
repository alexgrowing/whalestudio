import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCompNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalIntegralWeightSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.LowNonzero

theorem gapGe_wt_add_parWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (P : WtPar Dw) (hB : WtBig P) (j : ℕ) (w : Psi H → ℤ) :
    GapGe (((FlagTan.dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (P.wt j + GlobalTheory.FlatLine.parWt Dw w - FlagTan.kap Dw) := by
  intro τ k hk
  have a := (gaps_of_wtBig _ _ _ P hB P.u₁ (by simp)).1 τ k hk
  have hg := hB.gaps τ k hk
  have b := (P.gap_rem τ k).1
  have c : gap (GlobalTheory.FlatLine.parWt Dw w τ) k = 0 := by
    simp [gap, GlobalTheory.FlatLine.parWt]
  have hC0 : (0 : ℤ) ≤ (((FlagTan.dimFlag Dw + 1).choose 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hD0 : (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ (Dw.p : ℤ) := Int.natCast_nonneg _
  have hq0 : (0 : ℤ) ≤ (Dw.q : ℤ) := Int.natCast_nonneg _
  have e1 := mul_nonneg hD0 (le_trans zero_le_one a)
  have e2 := mul_nonneg (Int.natCast_nonneg j) (le_trans zero_le_one a)
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, gap_add, gap_sub, gap_nsmul, c]
  push_cast at hg ⊢
  nlinarith [mul_nonneg hD0 hC0, mul_nonneg hD0 hp0, mul_nonneg hD0 hq0, mul_nonneg hD0 hD0]

open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.Vanishing.H0 ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory in

theorem ne_zero_of_noBase {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {hB : B.IsLB}
    {W : Submodule k (H0 p B ⊤)} {U : Y.Opens} (h : NoBase hB W U) (hU : (U : Set Y).Nonempty) : ∃ f ∈ W, f ≠ 0 := by
  obtain ⟨y, hy⟩ := hU
  by_contra hne
  push Not at hne
  refine h y hy ((mem_support_baseIdeal hB W y).2 fun s hs hy' => ?_)
  obtain ⟨i, hi⟩ := exists_chart hB y
  have hu := (isUnit_ger_iff _ hi).2 hy'
  rw [ger_toSec, hne s hs, map_zero] at hu
  exact not_isUnit_zero hu

theorem exists_cusp_ne_zero (hP : Hypotheses2) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hT : GlobalTheory.Published.ToroidalChartsForFan)
    (hN : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7}
    {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hD : 1 ≤ FlagTan.dimFlag (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j))
    (hla : GapGe (((FlagTan.dimFlag (T.Q.Dw j) + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap (T.Q.Dw j))) :
    ∃ f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0), f ≠ 0 := by
  have hP1 := GlobalTheory.T.stronger_published_hypotheses_imply hP
  obtain ⟨TF⟩ := GlobalTheory.T.toroidal_flag_nonempty hP1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have hfree := GlobalTheory.T.toroidal_integral_weight_section hP1 hG hQ hP.q15 hP.q16 hS hT hN _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ hla
    ⟨GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace _ _ _ Y _ _ hY hf Z TF _, vanBd_le_space _ _ _ Y _ _ hY hf Z TF _⟩
  haveI := (GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hY.geo).2.2
  haveI : ConnectedSpace (Y₀ TF.X Z) := GeometricallyConnected.connectedSpace_of_subsingleton (str₀ TF.X Z)
  obtain ⟨s, hs, hs0⟩ := ne_zero_of_noBase hfree (dense_U₀ TF.X Z).nonempty
  refine ⟨(ofSpace TF.X Z Y.U _ ⟨s, hs⟩).1, (ofSpace TF.X Z Y.U _ ⟨s, hs⟩).2, fun h0 => hs0 ?_⟩
  have h1 : ofSpace TF.X Z Y.U _ ⟨s, hs⟩ = 0 := Subtype.ext h0
  exact congrArg Subtype.val (ofSpace_injective TF.X Z Y.U _ (h1.trans (map_zero _).symm))

theorem exists_cusp_uM : GlobalTheory.Published.ScholzeWeinsteinB → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → Covers fun Fm x _ ι p i Y _ _ => ∃ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ f ∈ cuspOn Y.U Z (wtOf (dat p i) (uM p i) 0), f ≠ 0 := by
  intro _ hP hG hQ hS hT hN
  have R := GlobalTheory.T.weight_conditions_at_index
  have W := GlobalTheory.T.weight_parameter_strict_antitone GlobalTheory.CovTop.SizeRows.size
  have B := wtBig_run
  unfold Covers Lifts at *
  refine (R.and (W.and B)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and (e2.and e3)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, -, -, hf, hj, -⟩ := hA i hi
  obtain ⟨-, -, -, -, -, ⟨w, -, hw⟩, -⟩ := hB i hi
  have hbig := hC i hi
  obtain ⟨Z⟩ := GlobalTheory.CovTop.good_comp_nonempty _ p.T hL _ hj Y _ _ hY.1
  refine ⟨Z, exists_cusp_ne_zero hP hG hQ hS hT hN Y hY.1 hf hbig.one_le Z _ ?_⟩
  rw [hw]
  exact gapGe_wt_add_parWt _ hbig _ w

end GlobalTheory.CovTop.LowNonzero

end
