import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
  Formalism.L2.SG.Pf.AmpWinLoc Formalism.L2.SG.Pf.WuDec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem muN_eq_const_mul_pi_trI : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ u : D.what₂.Word, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ A : Set X.B.I.Ginf, MeasurableSet A →
      X.muN u A = c * Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) := by
  intro D X C hB hG u
  choose hsfN hsfH hN hH hH1 hconc β hβm hβ1 hloc using
    Formalism.L2.SG.Pf.AmpWinGlob.place_all C u hG.1 hB
  have hpiN : Set.pi Set.univ (Nloc X u) = X.NinfU u := by
    ext s; simp only [Set.mem_pi, Set.mem_univ, true_implies]; exact Iff.rfl
  obtain ⟨h1, h2, h3, h4⟩ := X.muN_haar u
  obtain ⟨cN, hcN0, hcNt, hcN⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (Set.pi Set.univ (Nloc X u))
    (isClosed_set_pi fun v _ => (place_facts X u v).1) (QPK.isGrp_pi _ fun v => (place_facts X u v).2.2.1)
    (X.muN u) (Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C)) ⟨h1, h2, by rw [hpiN]; exact h3, by rw [hpiN]; exact h4⟩
    (QPK.invOn_pi _ _ hN)
  obtain ⟨hemb, hmapT⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C (fun v => hsfN v) one_pos
  refine ⟨cN, hcN0, hcNt, fun A _ => ?_⟩
  have htr : trI C = Formalism.L2.SG.LoopTerm.trInf C := rfl
  have hcov : Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C) A =
      Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) := by
    rw [htr, show Measure.pi (fun _ : D.what₂.Tau => muNB D 1) = Formalism.L2.SG.LoopTerm.dnB D 1 from rfl, ← hmapT,
      hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
  rw [hcN, Measure.smul_apply, smul_eq_mul, hcov]

end GlobalTheory
