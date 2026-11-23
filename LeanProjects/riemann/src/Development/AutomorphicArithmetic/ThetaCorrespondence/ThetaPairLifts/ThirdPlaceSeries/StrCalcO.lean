import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.StrCalcO
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieAutAndSplit
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigStrCalc
end GlobalTheory.EigStrCalc
namespace GlobalTheory.EigStrCalc
end GlobalTheory.EigStrCalc
namespace GlobalTheory.EigStrCalc
theorem is_split_of_cusp_iso_bcv : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (Q P0 : D.naut.AV i) (Sig : List (Part D.naut.CG)), D.naut.ptV i Q = some x → D.naut.ptV i P0 = some x → IsCuspIso D.nd D.naut Sig → IsBCV D.nd D.naut i P0 (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) → ∀ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → w ∉ D.nd.S i → w ∉ D.nd.Q i → D.naut.unr (D.naut.locV i Q w) → ∀ z : ℂ, D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {z⁻¹} → ∃ B' : Multiset ℂ, (D.naut.frobEig (D.naut.locV i Q w)).map (fun a : ℂ => a⁻¹) = B' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) z D.R.t ∧ ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  intro hAF hL D P h41 h7 _ i x Q P0 Sig hQ hP0 hSig hB w hsplit hS hQw hunr z hz
  have hsp : IsSplitPl D.host w := isSplitPl_of_under D w hsplit
  obtain ⟨π, rfl⟩ := hSig
  have e1 : D.naut.locV i Q w = D.naut.locV i P0 w :=
    (((h41 i).2.1 Q P0 (by rw [hQ]; exact Option.some_ne_none x) (hQ.trans hP0.symm)).2 w hS hQw).1 hsp
  have e2 := hB.2.2.2.1 w hsp
  have e3 : isoLoc D.nd D.naut (twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w =
      D.naut.lpSum (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)
        (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) := by
    have : spehLoc D.nd D.naut ⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ w = D.naut.locG (D.naut.tw π D.naut.etaTinv) w := by
      simp [spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]
    rw [← this]
    exact congrArg _ (D.naut.lpSum_zero _)
  have eV : D.naut.locV i Q w = D.naut.lpSum (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)
      (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) := by
    rw [e1, ← e2, e3]
  rw [eV] at hunr
  obtain ⟨ha, hb⟩ := (D.naut.unr_sum _ _).1 hunr
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hθ := unr_of_speh D.naut _ D.R.t ht w hb
  obtain ⟨-, hblk⟩ := GlobalTheory.RowModelRoad.frobEig_block D.naut _ D.R.t w z⁻¹ hθ hz
  refine ⟨(D.naut.frobEig (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)).map (fun a : ℂ => a⁻¹), ?_, ?_⟩
  · rw [eV, D.naut.frobEig_sum _ _ ha hb, Multiset.map_add, hblk, ← normV_eq_absNorm, inv_block]
  ·
    obtain ⟨hTie, -⟩ := _root_.GlobalTheory.AutomorphismSplitting.tieAut_and_split_alt hAF hL D P
    have hEta : GlobalTheory.LocalInv.EtaType D.nd D.naut := by
      refine ⟨hTie.1.1, fun τ z hz => ?_⟩
      rcases (hTie.2.1 τ).1 with h | h <;> rw [h, Multiset.mem_singleton] at hz <;> subst hz
      · exact ⟨0, by push_cast; ring⟩
      · exact ⟨-1, by push_cast; ring⟩
    have hmem : (⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ : Part D.naut.CG) ∈
        twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv := by
      simp [twistIso]
    obtain ⟨hcsd, hralg⟩ := GlobalTheory.LocalInv.part_alg D.nd D.naut hEta (GlobalTheory.LocalInv.weightRegular_definite D) i P0 _ hB _ hmem
      (odd_rank D.R) odd_one
    intro a haB
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp haB
    exact (((_root_.UpperTheory.GalN.tempo' h7 D.R.r _ (odd_rank D.R).pos hcsd hralg w).part_tw hTie ha α hα).1.inv
      (UpperTheory.GalN.one_lt_q w)).le_rpow (UpperTheory.GalN.one_lt_q w) (UpperTheory.GalN.half_le_r D.R)
end GlobalTheory.EigStrCalc
end
