import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistableStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPointStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FlagPieces

theorem sizesLe_stepLe (I : AutInst) (x : I.GA) {t : ℝ} (ht : 0 < t)
    (A' : Submodule (𝓞 I.E) (Fin I.n → I.E)) : SizesLe I x (stepLe I x t) A' t := by
  intro N _ hN hne
  have hle : stepLe I x t ≤ lamX I x := GlobalTheory.PointFlag.stepLe_le I x t
  have hne0 : stepLe I x t ≠ ⊥ := by
    intro h0
    apply hne
    rw [h0] at hN ⊢
    exact le_bot_iff.mp hN.1
  exact (GlobalTheory.PointFlag.sizeQ_le I x hle hN hne).trans ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t ht).2.2.2.2.1 hne0)

theorem perpIn_bot (I : AutInst) (x : I.GA) : perpIn I x ⊥ = lamX I x := by
  apply le_antisymm
  · exact Submodule.span_le.mpr fun y hy => hy.1
  · intro y hy
    apply Submodule.subset_span
    refine ⟨hy, fun s hs => ?_⟩
    rw [(Submodule.mem_bot _).mp hs]
    simp [Formalism.UG.hform]

theorem flag_pieces : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i, SatX I x (S i) ∧ SatX I x (perpIn I x (S i)) ∧ S i ≤ perpIn I x (S (Fin.last a)) ∧ perpIn I x (S (Fin.last a)) ≤ perpIn I x (S i) ∧ rkK (perpIn I x (S i)) + rkK (S i) = I.n) ∧ perpIn I x (S 0) = lamX I x ∧ SizesLe I x (perpIn I x (S (Fin.last a))) (S (Fin.last a)) 2 ∧ ∀ i : Fin a, SizesGe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (perpIn I x (S i.castSucc)) (perpIn I x (S i.succ)) (τ i)⁻¹ ∧ S i.succ ≠ ⊥ ∧ largestSize (bas I) (frm I x) (S i.succ) ≤ τ i ∧ SizesGe I x (lamX I x) (S i.succ) (if h : (i : ℕ) + 1 < a then τ ⟨i + 1, h⟩ else 1 / 2) := by
  intro I x a S τ hF
  have h35 := GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x
  have h34 := (GlobalTheory.T.canonicalFlag_exists_unique_semistable I x).2.2 a S τ hF
  have hsat : ∀ m, SatX I x (S m) := fun m => GlobalTheory.PointFlag.flag_sat hF m
  have hperpLast : perpIn I x (S (Fin.last a)) = stepLe I x 2 := by
    rw [hF.2.2.1, (h35.2.2.1 (1 / 2) (by norm_num)).2]
    norm_num
  have hle_last : ∀ i, S i ≤ S (Fin.last a) := fun i => hF.2.1.monotone (Fin.le_last i)
  have hlast_le : S (Fin.last a) ≤ stepLe I x 2 := by
    rw [hF.2.2.1]
    exact (GlobalTheory.PointFlag.stepLt_le_stepLe I x _).trans (GlobalTheory.PointFlag.stepLe_mono I x (by norm_num))
  refine ⟨fun i => ?_, ?_, ?_, fun i => ?_⟩
  · have hp := h35.2.2.2 (S i) (S i) (hsat i) (hsat i) le_rfl
    have hp' := h35.2.2.2 (S i) (S (Fin.last a)) (hsat i) (hsat _) (hle_last i)
    refine ⟨hsat i, hp.1, ?_, hp'.2.2.2.1, hp.2.1⟩
    rw [hperpLast]
    exact (hle_last i).trans hlast_le
  · rw [hF.1]
    exact GlobalTheory.FlagPieces.perpIn_bot I x
  · rw [hperpLast]
    exact GlobalTheory.FlagPieces.sizesLe_stepLe I x (by norm_num) _
  · obtain ⟨hcs, _, hlarge, hge, hlei⟩ := h34.1 i
    obtain ⟨hτpos, _, hsucc, _⟩ := hF.2.2.2.2.1 i
    have hsuccle : S i.succ ≤ lamX I x := by
      rw [hsucc]
      exact GlobalTheory.PointFlag.stepLe_le I x _
    refine ⟨?_, hlei, ?_, ?_, hlarge.le, ?_⟩
    · intro N hlt hle
      exact hge N hlt (hle.trans hsuccle)
    · rw [hcs, hsucc, (h35.2.2.1 _ hτpos).1, (h35.2.2.1 _ hτpos).2]
      exact GlobalTheory.FlagPieces.sizesLe_stepLe I x (inv_pos.mpr hτpos) _
    · intro h
      have hlt : S i.castSucc < S i.succ := hF.2.1 (Fin.castSucc_lt_succ ..)
      rw [h] at hlt
      exact not_lt_bot hlt
    · split_ifs with h
      · have e : (⟨(i : ℕ) + 1, h⟩ : Fin a).castSucc = i.succ := Fin.ext (by simp)
        have hn := (h34.1 ⟨(i : ℕ) + 1, h⟩).2.2.2.1
        rw [e] at hn
        intro N hlt hle
        exact hn N hlt hle
      · have hi := i.isLt
        have e : i.succ = Fin.last a := Fin.ext (by simp; omega)
        rw [e, hF.2.2.1]
        intro N hlt hle
        exact (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.1 N hlt hle

end GlobalTheory.FlagPieces
