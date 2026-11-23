import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.RankOneOfLong
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParamEqUbcSatVStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValInertStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StrInertTyz
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieAutAndSplit
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.UbcString
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
end GlobalTheory.UbcString
theorem GlobalTheory.UbcString.ubc_string_o_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc), ∀ x ∈ ZgoodN D.nd D.naut i, ∃ P', D.naut.ptV i P' = some x ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ (B'' : Multiset ℂ) (c : ℂ), D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {c} ∧ ubc D.R.nV (D.naut.satV i P' w) = B'' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) c D.R.t ∧ ∀ a ∈ B'', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  intro hAF hL D P X _ _ h7 htie i x hx
  obtain ⟨-, Sig, ⟨P', hP', hB⟩, hgood⟩ := hx
  obtain ⟨π, rfl⟩ := GlobalTheory.T.goodLabels_rank_part_parameter_cuspidal D htie i x Sig ⟨P', hP', hB⟩ hgood
  refine ⟨P', hP', fun w hw => ?_⟩
  have hns := GlobalTheory.UbcString.not_isSplitPl_of_inert D.host w hw
  obtain ⟨hunr, hfe⟩ := hB.2.2.2.2.1 w hns
  have e1 : spehLoc D.nd D.naut ⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ w =
      D.naut.locG (D.naut.tw π D.naut.etaTinv) w := by
    simp [spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]
  have e : isoLoc D.nd D.naut (twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w =
      D.naut.lpSum (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)
        (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) := by
    simp only [isoLoc, twistIso, muPart, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, D.naut.lpSum_zero, e1]
  rw [e] at hunr hfe
  obtain ⟨ha, hb⟩ := (D.naut.unr_sum _ _).1 hunr
  have hb' : D.naut.unr ((List.range D.R.t).map (fun a : ℕ => (a : ℝ)) |>.foldr
      (fun k acc => D.naut.lpSum (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)
        (((D.R.t : ℝ) - 1) / 2 - k)) acc) (D.naut.lpZero w)) := by
    rw [← GlobalTheory.LocalInv.list_coe]; exact hb
  have hm : D.naut.unr (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) :=
    GlobalTheory.UbcString.unr_of_foldr D.naut _ (fun k : ℝ => ((D.R.t : ℝ) - 1) / 2 - k) _ 0
      (List.mem_map.2 ⟨0, List.mem_range.2 D.R.t_odd.pos, by simp⟩) hb'
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1
    (by rw [D.naut.frobEig_card _ hm, D.naut.locG_dim] :
      Multiset.card (D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)) = 1)
  have hstr : D.naut.frobEig (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) =
      GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) c D.R.t := by
    have h := (GlobalTheory.UbcString.frobEig_foldr D.naut _ hm (fun k : ℝ => ((D.R.t : ℝ) - 1) / 2 - k)
      ((List.range D.R.t).map (fun a : ℕ => (a : ℝ)))).2
    unfold spehLoc
    rw [GlobalTheory.LocalInv.list_coe]
    refine h.trans ?_
    rw [hc]
    simp only [Multiset.map_singleton]
    rw [List.map_map, Function.comp_def, GlobalTheory.UbcString.sum_singletons (fun a : ℕ => c * ((normV w : ℕ) : ℂ) ^ ((((D.R.t : ℝ) - 1) / 2 - (a : ℝ) : ℝ) : ℂ)), GlobalTheory.DownLift.str, Multiset.range, Multiset.map_coe]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    have hq : ((normV w : ℕ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) := rfl
    rw [hq]
    push_cast
    ring_nf
  rw [D.naut.frobEig_sum _ _ ha hb, hstr] at hfe
  refine ⟨D.naut.frobEig (D.naut.locG (D.naut.tw π D.naut.etaTinv) w), c, hc, hfe.symm, ?_⟩
  have hAut := (_root_.GlobalTheory.AutomorphismSplitting.tieAut_and_split_alt hAF hL D P).1
  have hη : GlobalTheory.LocalInv.EtaType D.nd D.naut := by
    obtain ⟨⟨h1, -⟩, h2, -⟩ := hAut
    refine ⟨h1, fun τ z hz => ?_⟩
    rcases (h2 τ).1 with e | e <;> rw [e, Multiset.mem_singleton] at hz <;> subst hz
    · exact ⟨0, by simp⟩
    · exact ⟨-1, by push_cast; ring⟩
  have hpa := GlobalTheory.LocalInv.part_alg D.nd D.naut hη (GlobalTheory.LocalInv.weightRegular_definite D) i P' _ hB
    ⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ (by simp [twistIso]) (GlobalTheory.LocalInv.r_odd D.R) odd_one
  intro α hα
  exact ((_root_.UpperTheory.GalN.tempo' h7 D.R.r _ (GlobalTheory.LocalInv.r_odd D.R).pos hpa.1 hpa.2 w).part_tw hAut ha α hα).1.le_rpow
    (UpperTheory.GalN.one_lt_q w) (UpperTheory.GalN.half_le_r D.R)
theorem GlobalTheory.EigStrInert.str_inert_tyz : _root_.GlobalTheory.EigStrInert.strInert_tyz := by
  intro hA hL D P X hAg hconds hadm htie i hμ j hj x hx f hf y hy hy0 h hh s B hE hB w hw hinert
  obtain ⟨P', hP', hw2⟩ := _root_.GlobalTheory.UbcString.ubc_string_o_alt hA hL D P X hAg hconds hadm htie i x hx
  obtain ⟨B'', c, hc, heq, hnorm⟩ := hw2 w hinert
  have h1 := _root_.GlobalTheory.T.theta_eigen_compatibility_seventh_alt hA hL D P X hAg hconds hadm htie i hμ j hj x hx f hf y hy hy0 h hh s B hE hB w hw hinert P' hP'
  have h2 := _root_.GlobalTheory.T.good_place_split_condition_alt hA hL D P X hAg hconds hadm htie i hμ j hj w hw hinert c hc
  exact ⟨B'', by rw [h1, heq, h2], hnorm⟩
end
